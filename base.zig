// ===========================================================
// This file must only be shared with accompanying
// licence file: LICENCE.txt
// Author: Joshua Lewis Hayes <joshua@hayesandassociates.uk>
// License: MIT
// ===========================================================

const std = @import("std");
const ArrayList = std.ArrayList;
const LinkedList = std.SinglyLinkedList;
const HashMap = std.StringHashMap;
const Allocator = std.mem.Allocator;

const ImmutableAssignments = false;
const MaxDepth = 300;

// === Assignment Parameters ===
// In order to be as flexible as possible and allow for userland access
// to lambdas and error streams, the assignment directly contains the
// assignment name and the Resolved Action type.
const Assignment = struct {
    name: []const u8,
    value: ResolvedAction,
};

// === Closures ===
// Since there are extremely powerful structures that can contain their
// own scope, values and operations, this system is built around implementing
// functions as closures directly, allowing for significant flexibilty and
// the possibility of user generated functions and partial application.
// NOTICE: Current limitation of zig prevents structs from self referencing like
// is required to allow a lambda type signature that includes a lambda type signature
const Signature = struct {
    name: []const u8,
    argT: ArgumentTypes,
};

const ClosureT = struct {
    argumentList: ArrayList(Signature),
    returnType: ArgumentTypes,
};

const Closure = struct {
    typeSignature: ClosureT,
    procedures: ArrayList(Action),
};

// === Function Call Parameters ===
// Defines every valid type that can be received by a function, including
// scalar values, void, lambdas and error lists.
const ArgumentTypes = union(enum) {
    void: struct {},
    integer: i32,
    unsigned: u32,
    float: f32,
    boolean: bool,
    character: u8,
    string: []const u8,
    lambda: *const ClosureT,
    errlst: usize,
};

const CallParameters = struct {
    target: []const u8,
    arguments: ArrayList([]const u8),
    returnType: ArgumentTypes,
};

const Action = union(enum) {
    call: CallParameters,
    let: Assignment,
};

const ResolvedAction = union(enum) {
    integer: i32,
    unsigned: u32,
    float: f32,
    boolean: bool,
    character: u8,
    string: []const u8,
    call: CallParameters,
    lambda: Closure,
    errlst: ArrayList(ErrorEntry),
    void: struct {},
};

// === Type Resolution ===
// As this system uses encapsulated data, there must be a solution for
// extracting the type information from a particular value, especially
// for lambdas with their embedded type signatures
pub fn getType(ra: ResolvedAction) ArgumentTypes {
    return switch (ra) {
        .integer => ArgumentTypes{ .integer = -1 },
        .unsigned => ArgumentTypes{ .unsigned = 0 },
        .float => ArgumentTypes{ .float = 1.0 },
        .boolean => ArgumentTypes{ .boolean = true },
        .character => ArgumentTypes{ .character = 'A' },
        .string => ArgumentTypes{ .string = "" },
        .call => |c| c.returnType,
        .lambda => |l| ArgumentTypes{ .lambda = &l.typeSignature },
        .errlst => |e| ArgumentTypes{ .errlst = e.items.len },
        .void => ArgumentTypes{ .void = .{} },
    };
}

pub fn isAcceptedType(t1: ArgumentTypes, t2: ArgumentTypes) bool {
    return switch (t2) {
        .void => switch (t1) {
            .void => true,
            else => false,
        },
        .lambda => |l2| switch (t1) {
            .lambda => |l1| (l1 == l2),
            else => false,
        },
        .errlst => switch (t1) {
            .errlst => true,
            else => false,
        },
        .integer => switch (t1) {
            .integer => true,
            else => false,
        },
        .unsigned => switch (t1) {
            .unsigned => true,
            else => false,
        },
        .float => switch (t1) {
            .float => true,
            else => false,
        },
        .boolean => switch (t1) {
            .boolean => true,
            else => false,
        },
        .character => switch (t1) {
            .character => true,
            else => false,
        },
        .string => switch (t1) {
            .string => true,
            else => false,
        },
    };
}

// === Error Handling and Generation ===
// A simple set of handlers for generating error messages
// consistantly whilst improving general code hygiene
const ErrorEntry = struct {
    target: []const u8,
    msg: []const u8,
};

fn makeError(target: []const u8, msg: []const u8, alloc: *Allocator) ResolvedAction {
    var errLst = ArrayList(ErrorEntry).initCapacity(alloc, 1) catch {
        return ResolvedAction{ .void = .{} };
    };
    var errEntry = ErrorEntry{
        .target = target,
        .msg = msg,
    };
    errLst.appendAssumeCapacity(errEntry);
    return ResolvedAction{ .errlst = errLst };
}

fn appendError(ra: *ResolvedAction, target: []const u8, msg: []const u8, alloc: *Allocator) ResolvedAction {
    switch (ra.*) {
        .errlst => {
            var errEntry = ErrorEntry{ .target = target, .msg = msg };
            var originalLength = ra.errlst.capacity;
            var newErrorList = ArrayList(ErrorEntry).initCapacity(alloc, ra.errlst.capacity + 1) catch
                return makeError(target, "Not enough memory to reallocate error list", alloc);
            newErrorList.appendSliceAssumeCapacity(ra.errlst.toOwnedSlice());
            newErrorList.appendAssumeCapacity(errEntry);
            ra.errlst.deinit();
            return ResolvedAction{ .errlst = newErrorList };
        },
        else => return makeError(target, msg, alloc),
    }
}

// === Assignment Call Execution ===
// As an assignment can be any of the following: Scalar Value, Lambda, Error List
// the call to retrieve those values has to be flexible enough to accomodate that
fn call(c: CallParameters, scopes: *ArrayList(*HashMap(Assignment)), alloc: *Allocator) ResolvedAction {
    // Search for function in available scopes
    var function = retrieveAssignment(c.target, scopes);
    if (function == null)
        return makeError(c.target, "Assignment value is not defined in accessible scopes", alloc);

    // Check if value is scalar or error and return if so
    switch (function.?.value) {
        .lambda => |l| {
            if (isAcceptedType(l.typeSignature.returnType, c.returnType)) {
                var res = apply(l, c.arguments, scopes, alloc);
                var resT = getType(res);
                if (isAcceptedType(resT, l.typeSignature.returnType)) {
                    return res;
                } else {
                    return appendError(&res, c.target, "Lambda failed to match promised return type", alloc);
                }
            } else {
                return makeError(c.target, "Lambda return type is not accepted by call return type", alloc);
            }
        },
        .call => |c1| return call(c1, scopes, alloc),
        else => return function.?.value,
    }
}

// === Argument Type Checkng and Assignment ===
// While it's not ideal to combine Assignment with Type Checking, it reduces the number of
// times the argument has to be iterated over, helping with performance in larger programs
fn typeCheckAndScope(args: *ArrayList(ResolvedAction), typeSig: ClosureT, scope: *HashMap(Assignment)) ?ErrorEntry {
    for (args.items) |arg, index| {
        var tmp = typeSig.argumentList.items[index];
        if (isAcceptedType(getType(arg), tmp.argT)) {
            return ErrorEntry{ .target = tmp.name, .msg = "Argument does not match expected type" };
        } else {
            if (ImmutableAssignments and newScope.contains(tmp.name)) {
                return ErrorEntry{ .target = tmp.name, .msg = "Assignment already exists in this scope" };
            } else {
                scope.*.put(tmp.name, Assignment{
                    .name = tmp.name,
                    .value = arg,
                }) catch
                    return ErrorEntry{ .target = tmp.name, .msg = "Failed to add value to scope" };
            }
        }
    }
    return null;
}

// === Lambda Function Application ===
// By treating every function call as a lambda, it greatly simplifies the interface
// and allows for first class function definition without requiring an assignment,
// this is particularly essential for partial application and monad implementation
fn apply(lambda: Closure, argList: ArrayList([]const u8), scopes: *ArrayList(*HashMap(Assignment)), alloc: *Allocator) ResolvedAction {
    if (argList.capacity != lambda.typeSignature.argumentList.capacity)
        return makeError("Apply", "Function expects a different number of arguments", alloc);

    // Try and find arguments in list and place in newly allocated memory
    // or fail and deallocate with defer
    var arguments = ArrayList(Assignment).initCapacity(alloc, argList.capacity) catch
        return makeError("Apply", "Argument List Allocation Failed", alloc);
    defer arguments.deinit();
    for (argList.items) |arg| {
        if (retrieveAssignment(arg, scopes)) |ass| {
            arguments.append(ass) catch
                return makeError(arg, "Failed to append acquired argument to ArrayList", alloc);
        } else {
            return makeError(arg, "Argument not found in accessible scope", alloc);
        }
    }

    // Resolve arguments to scalar or lambda values to newly allocated memory,
    // or fail and deallocate with defer
    var resolvedArgs = ArrayList(ResolvedAction).initCapacity(alloc, arguments.capacity) catch
        return makeError("Apply", "Resolved Argument List Allocation Failed", alloc);
    defer resolvedArgs.deinit();
    for (arguments.items) |arg| {
        resolvedArgs.append(resolve(arg.value, scopes, alloc)) catch
            return makeError(arg.name, "Failed to append resolved value to ArrayList", alloc);
    }

    // Type check resolved values against closure type signature and assign to scope
    // or fail and deallocate with defer
    var newScope = HashMap(Assignment).init(alloc);
    defer newScope.deinit();
    if (typeCheckAndScope(&resolvedArgs, lambda.typeSignature, &newScope)) |err| {
        return makeError(err.target, err.msg, alloc);
    }

    // Begin closure execution with new scope
    return execute(lambda, &newScope, scopes, alloc);
}

// It's worth noting that due to how ArrayList works, the Array is actually
// ordered in oldest to newest, so the scope searches have to be done in reverse
fn retrieveAssignment(key: []const u8, scopes: *ArrayList(*HashMap(Assignment))) ?Assignment {
    var assignment: ?Assignment = null;
    var iterator = scopes.capacity;
    var scopePointers = scopes.items;
    while (iterator >= 0) : (iterator -= 1) {
        if (scopePointers[iterator].*.get(key)) |func| {
            assignment = func;
            break;
        }
    }
    return assignment;
}

// === Closure Execution ===
// As a closure can contain multiple state manipulating procedures, the
// execution function has to be able to maintain that state of the current
// scope as well as be able to pull from higher scopes for function calls.
// It also has to be able to always return a value, and since any function
// could set the return value it has to be given a known name, this means
// generating an assigment and always checking its value when the user returns.
fn execute(lambda: Closure, current: *HashMap(Assignment), scopes: *ArrayList(*HashMap(Assignment)), alloc: *Allocator) ResolvedAction {
    scopes.ensureCapacity(scopes.capacity + 1) catch
        return makeError("Lambda", "Not Enough Memory to extend scopes", alloc);
    scopes.appendAssumeCapacity(current);
    defer _ = scopes.pop();
    for (lambda.procedures.items) |proc| {
        _ = switch (proc) {
            .let => |l| if (ImmutableAssignments and current.contains(l.name)) {
                return makeError(l.name, "Assignment already exists in this scope", alloc);
            } else {
                current.put(l.name, Assignment{ .name = l.name, .value = resolve(l.value, scopes, alloc) }) catch {
                    return makeError(l.name, "Failed to assign to current scope", alloc);
                };
            },
            .call => |c| _ = call(c, scopes, alloc),
        };
        if (current.get("lambda_return_value")) |ret| {
            if (isAcceptedType(getType(ret.value), lambda.typeSignature.returnType)) {
                return ret.value;
            } else {
                return makeError(ret.name, "Value does not match expected return type", alloc);
            }
        }
    }
    current.deinit();
    return ResolvedAction{ .void = .{} };
}

fn resolve(ra: ResolvedAction, scopes: *ArrayList(*HashMap(Assignment)), alloc: *Allocator) ResolvedAction {
    var res = ra;
    var depth: usize = 0;
    while (true) {
        res = switch (res) {
            // This does have the possibility of an infinitely recursive
            // execution flow, but passing the current function name
            // and/or all parent names would break lambda usage and
            // allowing this is required to allow for name aliasing
            .call => |c| if (depth < MaxDepth) call(c, scopes, alloc) else makeError("Resolution", "Program Reached Max Call Depth", alloc),
            else => break,
        };
    }
    return res;
}

// === Debug Functions ===
// As most debugging is rather challenging to do at compile time
// these functions are specifically intended to stringify values
// for console level debugging output.
fn concatStrings(arr: ArrayList([]const u8), alloc: *Allocator) Allocator.Error![]const u8 {
    var length: usize = 0;
    for (arr.items) |str| {
        length += str.len;
    }
    var buffer = try alloc.alloc(u8, length);
    length = 0;
    for (arr.items) |str| {
        std.mem.copy(u8, buffer[length..], str);
        length += str.len;
    }
    return buffer;
}

fn lambdaTypeString(cT: *const ClosureT, alloc: *Allocator) Allocator.Error![]const u8 {
    var argStrings = ArrayList([]const u8).init(alloc);
    defer argStrings.deinit();
    try argStrings.append("Lambda: (");
    for (cT.argumentList.items) |sig| {
        var tyStr = try typeString(sig.argT, alloc);
        try argStrings.append(tyStr);
        try argStrings.append(" -> ");
    }
    var retStr = try typeString(cT.returnType, alloc);
    try argStrings.append(retStr);
    try argStrings.append(")");
    var str = concatStrings(argStrings, alloc);
    alloc.free(retStr);
    return str;
}

fn printErrorList(errlst: ArrayList(ErrorEntry)) !void {
    const stdout = std.io.getStdOut().writer();
    try stdout.print("Error List:\n", .{});
    for (errlst.items) |errorEntry| {
        try stdout.print("[Target: {}] Message: {}.\n", .{ errorEntry.target, errorEntry.msg });
    }
}

// This has to copy any compile time known strings into a buffer to
// ensure a consistant interface, otherwise the caller would have
// to check the type of t to see if it was a lambda, which would
// be the only option that does allocate memory.
fn mkBuffer(str: []const u8, alloc: *Allocator) Allocator.Error![]const u8 {
    var buffer = try alloc.alloc(u8, str.len);
    std.mem.copy(u8, buffer[0..], str);
    return buffer;
}

fn typeString(t: ArgumentTypes, alloc: *Allocator) Allocator.Error![]const u8 {
    return switch (t) {
        .lambda => |l| lambdaTypeString(l, alloc),
        .errlst => mkBuffer("Error List", alloc),
        .void => mkBuffer("Void", alloc),
        .integer => mkBuffer("Integer", alloc),
        .unsigned => mkBuffer("Unsigned", alloc),
        .float => mkBuffer("Float", alloc),
        .boolean => mkBuffer("Boolean", alloc),
        .character => mkBuffer("Character", alloc),
        .string => mkBuffer("String", alloc),
    };
}

// === Unit Testing ===
// As with any program, proper functionally must be ensured and
// zig's inbuilt unit testing facility makes this easy as can
// be seen below.
test "Type checking tests" {
    var alloc = std.testing.allocator;
    var a = ResolvedAction{ .void = .{} };
    var b = ResolvedAction{ .integer = 5 };
    var c = ResolvedAction{
        .call = CallParameters{
            .target = "test",
            .arguments = ArrayList([]const u8).init(alloc),
            .returnType = ArgumentTypes{ .void = .{} },
        },
    };
    var d = ResolvedAction{
        .lambda = Closure{
            .typeSignature = ClosureT{
                .argumentList = ArrayList(Signature).init(alloc),
                .returnType = ArgumentTypes{ .void = .{} },
            },
            .procedures = ArrayList(Action).init(alloc),
        },
    };
    const stdout = std.io.getStdOut().writer();
    var aTS = try typeString(getType(a), alloc);
    try stdout.print("\nThe value of 'a' is of type: [{}]\n", .{aTS});
    std.testing.expect(isAcceptedType(getType(a), ArgumentTypes{ .void = .{} }));
    alloc.free(aTS);

    var bTS = try typeString(getType(b), alloc);
    try stdout.print("The value of 'b' is of type: [{}]\n", .{bTS});
    std.testing.expect(isAcceptedType(getType(b), ArgumentTypes{ .integer = -1 }));
    alloc.free(bTS);

    var cTS = try typeString(getType(c), alloc);
    try stdout.print("The value of 'c' is of type: [{}]\n", .{cTS});
    std.testing.expect(isAcceptedType(getType(c), ArgumentTypes{ .void = .{} }));
    alloc.free(cTS);

    var dTS = try typeString(getType(d), alloc);
    try stdout.print("The value of 'd' is of type: [{}]\n", .{dTS});
    std.testing.expect(isAcceptedType(getType(d), getType(d)));
    alloc.free(dTS);
}

test "Simple Error" {
    var alloc = std.testing.allocator;
    var err = try ArrayList(ErrorEntry).initCapacity(alloc, 2);
    try err.append(ErrorEntry{
        .target = "Test 1",
        .msg = "Testing a single error",
    });
    try printErrorList(err);
    err.appendAssumeCapacity(ErrorEntry{
        .target = "Test 2",
        .msg = "Testing consequetive errors",
    });
    try printErrorList(err);
    err.deinit();
    var err3 = makeError("Test 3", "Testing makeError function", alloc);
    try printErrorList(err3.errlst);
    //var err4 = appendError(&err3, "Test 4", "Testing appendError function", alloc);
    err3.errlst.deinit();
    //err4.errlst.deinit();
}

test "Simple Execution" {
    var alloc = std.testing.allocator;
    var actions = [_]Action{
        Action{
            .let = Assignment{
                .name = "lambda_return_value",
                .value = ResolvedAction{ .integer = 5 },
            },
        },
    };
    var typeSig = ClosureT{
        .argumentList = ArrayList(Signature).init(alloc),
        .returnType = ArgumentTypes{ .integer = 0 },
    };
    var lambda = Closure{
        .typeSignature = typeSig,
        .procedures = ArrayList(Action).fromOwnedSlice(alloc, actions[0..]),
    };
    var currentScope = HashMap(Assignment).init(alloc);
    defer currentScope.deinit();
    var scopes = ArrayList(*HashMap(Assignment)).init(alloc);
    var result = execute(lambda, &currentScope, &scopes, alloc);
    scopes.deinit();
    var resT = getType(result);
    const stdout = std.io.getStdOut().writer();
    var tStr = try typeString(resT, alloc);
    defer alloc.free(tStr);
    try stdout.print("The returned value is of type: [{}]\n", .{tStr});
    if (isAcceptedType(resT, ArgumentTypes{ .errlst = 0 })) {
        try printErrorList(result.errlst);
    } else {
        std.testing.expect(isAcceptedType(resT, ArgumentTypes{ .integer = -1 }));
    }
}
