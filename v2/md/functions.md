# Functions and methods

## Moving a value into a call and back

````{example} functions.example.identity
:lean: Functions/Checks:identity

A function gives a sequence of statements its own parameters and locals. A call
transfers argument values into those parameters; a return transfers a result
back to the caller.

```dada
class Token {}

fn identity(token: → Token) → Token {
    return token→;
}

let original = new Token();
let result = identity(original→);
```

Here `→ Token` in a signature means [uniquely owned `Token`](shared-typing.md#claim-shared.typing.types), called `given
Token` in the model. The argument expression `original→` [empties `original`](shared.md#claim-shared.give).
The function receives that reference in `token`, then moves it into its return
value. The caller binds the same reference to `result`. No object is copied or
reconstructed.

The arrow after the parameter list introduces a uniquely owned
result type: `fn identity(...) → Token`. A shared result instead uses
`fn copy(...) shared Point`. This chapter uses
the same permission-prefixed type syntax as parameters, without an additional
return-type separator.

This layer adds functions and methods to Shared. The examples check typing and
execution in Lean. The new rules come first; the explicit forward reference to
the [inherited machinery in the appendix](#claim-functions.inherited) keeps the
call rules together without repeating Shared's expression calculus here.
````

````{example} functions.example.shared
:lean: Functions/Checks:shared

A `shared` parameter receives an [owned shared reference](shared.md#claim-shared.references). It does not borrow
from the caller, and returning it does not create a dependency on the callee's
locals.

```dada
struct Point {}

fn copy(point: shared Point) shared Point {
    return point→;
}

let p = new Point();
let s = p→share;
let t = copy(s→);
```

Sharing empties the uniquely owned `p` and produces the shared reference `s`.
[Giving `s` copies it](shared.md#claim-shared.give), and giving the shared parameter `point` copies it again.
Both `s` and `t` remain initialized and refer to the same object.

`shared Point` means `shared[] Point`: shared ownership with no lease
dependency. The empty brackets may be omitted. [Classes cannot be shared](shared.md#claim-shared.struct), so a
parameter of type `shared Token` for the class in the preceding example is
invalid.
````

## Locals live in frames

````{example} functions.example.gc
:lean: Functions/Checks:gc

A suspended caller keeps its locals alive while another function runs:

```dada
class Token {}
class Box { child: Token }
fn work() {
    let temporary = new Token();
}
let box = new Box(new Token());
work();
```

The focused runtime check starts inside `work`, with the caller's box and its
child already allocated. It checks these transitions:

| Boundary | Frames | Heap |
| --- | --- | --- |
| After allocating `temporary` | `work`, initial caller | box, child, temporary |
| After returning from `work` | initial caller | box, child |
| After popping the initial frame | none | empty |

The box is rooted only by the suspended caller during `work`; its child is
reachable through a field. Both survive collection. The temporary is reclaimed
as soon as `work` returns. All three object identifiers remain spent: the final
allocation counter is three. The check also covers the single exit step of an
empty program.

These examples observe returned values **before** the final frame exits.
The [frame rules](#claim-functions.machine) and
[collector definition](#claim-functions.gc) below make this lifetime explicit.
The later Destructors layer will require consuming class values before a frame
can exit; this layer permits them to become unreachable.
````

## Methods choose a receiver permission

````{example} functions.example.methods
:lean: Functions/Checks:methods

A method belongs to a [nominal declaration](shared.md#claim-shared.declarations). Its first parameter names the
permission it requires for `self`; the enclosing declaration fixes the nominal
type of the receiver.

```dada
struct Point {
    fn take(→self) → Point {
        return self→;
    }
    fn copy(shared self) shared Point {
        return self→;
    }
}

let p = new Point();
let q = Point.take(p→);
let s = q→share;
let t = Point.copy(s→);
```

The `take` call gives `p` to an owned receiver. The `copy` call gives `s`, which
produces a shared copy, to a shared receiver. `p` becomes empty; `s` remains
initialized. Both receiver permissions use prefix syntax in declarations.
There is no general `self: Type` receiver form.

Each call names the enclosing type and method explicitly, with the receiver
as the first argument. The [give operation](shared.md#claim-shared.give) moves or copies according to the
receiver's permission. Method-call sugar is deferred to a later layer.
````

## Syntax

```{definition} functions.signatures
:lean: Functions/Syntax:Name Functions/Syntax:Parameter Functions/Syntax:Signature Functions/Syntax:receiver Functions/Syntax:Signature.WellFormed
:uses: shared.typing.types shared.struct

A *callable name* \\(a\\) identifies either a global function \\(f\\) or a method
named \\(m\\) of nominal type \\(C\\). Parameter names \\(x\\) are local variables. A
*signature type* \\(T\\) is a [whole nominal type](shared-typing.md#claim-shared.typing.types) with an explicit permission
\\(Q\\); it carries no partial view.

\\[
\begin{aligned}
a &::= f \mid C.m, & Q &::= {\to} \mid \mathsf{shared}, \\
T &::= Q\ C, & P &::= x:T, \\
R &::= \mathsf{none} \mid T, & \sigma &::= ({\overline P})\;R.
\end{aligned}
\\]

Here \\(P\\) is a parameter, \\(R\\) an optional result type, and
\\(\sigma\\) a signature.

`shared[]` abbreviates the same permission as `shared`. The model calls `→`
permission `given`. A result annotation follows the parameter list directly;
its absence denotes no result. There is no implicit parameter permission.

A method's first parameter is written `→self` or `shared self`. These elaborate
to the parameter named `self` with type `→ C` or `shared C`, respectively,
where `C` is the enclosing nominal type. No `self: Type` surface form is
provided. Ordinary function parameters cannot be named `self`.

A well-formed signature has distinct parameter names and [admissible parameter
and result types](shared-typing.md#claim-shared.typing.well_formed_types). A method must have its correctly named and typed receiver
first. In particular, classes admit only given access, shared structs admit
only shared access, and ordinary structs admit either.
```

```{definition} functions.calls
:lean: Functions/Syntax:Statement Functions/Syntax:Body Functions/Syntax:Declaration Functions/Syntax:Program
:uses: functions.signatures shared.syntax shared.typing.patterns

A *[value expression](shared.md#claim-shared.syntax)* \\(e\\) and *[binding pattern](shared-typing.md#claim-shared.typing.patterns)* \\(b\\) are inherited from
Shared (see the [appendix](#claim-functions.inherited)). An *optional call
destination* \\(d\\) is either a fresh local name or absent. The core syntax is:

\\[
\begin{aligned}
d &::= \mathsf{none}\mid x, \\
t &::= \mathsf{let}\ b=e \mid d\mathrel{:=}\mathsf{call}\ a({\overline e}), \\
r &::= \mathsf{none}\mid e, \\
B &::= ({\overline t};\ \mathsf{return}\ r), \\
D &::= (\sigma,B).
\end{aligned}
\\]

Here \\(t\\) is a statement, \\(r\\) an optional return expression, \\(B\\) a
body, and \\(D\\) a declaration pairing a [signature](#claim-functions.signatures) with its body. The call notation above is metasyntax:
`let x = f(args);` supplies destination `x`, while `f(args);` supplies none.
A method call is `C.method(receiver, args)`, with its receiver as argument zero.
There is no receiver-based call sugar.

A body stores its final return separately from its statement list. `return;`
and falling off the end both mean no return expression. There are no early
returns. Receivers, arguments, and returned values use call-free expressions;
write nested calls as successive statements.

A program contains a [nominal class table](shared-typing.md#claim-shared.typing.declarations) \\(\Delta\\), a declaration table
\\(F\\) listing callable-name/declaration pairs, and a top-level statement
list. Method lookup uses the qualified name, not runtime dispatch. There is
no overloading. These are abstract syntax definitions, not a source parser.
```

## Typing calls and bodies

```{definition} functions.environments
:lean: Functions/Syntax:Signature.environment
:uses: functions.signatures shared.typing.environments shared.typing.bindings

An *[environment](shared-typing.md#claim-shared.typing.environments)* \\(\Gamma\\) maps local names to types or empty slots.
Write \\(\operatorname{WF}_{\Delta}(\Gamma)\\) for the inherited check of
distinct names and normalized, admissible types.
Write \\(\operatorname{env}(\sigma)\\) for a [signature's parameter environment](#claim-functions.signatures):
each parameter is initially present at its declared whole type. Write
\\(\operatorname{params}(\sigma)\\) for its ordered parameter types and
\\(\operatorname{result}(\sigma)\\) for its optional result type.
```

```{definition} functions.destination_typing
:lean: Functions/Typing:DestinationTyped
:uses: functions.environments functions.calls shared.typing.bindings

The judgment \\(\Delta\vdash\Gamma;d:R\Rightarrow\Gamma'\\) installs a call's
result. An absent destination requires an absent result; a present one uses
[Shared's fresh-variable binding judgment](shared-typing.md#claim-shared.typing.bindings), written
\\(\Delta\vdash\Gamma;x:T\Rightarrow_{\mathrm{bind}}\Gamma'\\).

\\[
\frac{\operatorname{WF}_{\Delta}(\Gamma)}
 {\Delta\vdash\Gamma;\mathsf{none}:\mathsf{none}\Rightarrow\Gamma}
\qquad
\frac{\Delta\vdash\Gamma;x:T\Rightarrow_{\mathrm{bind}}\Gamma'}
 {\Delta\vdash\Gamma;x:T\Rightarrow\Gamma'}
\\]

A value-returning call cannot silently discard its result. The binding premise
also checks admissibility and freshness.
```

```{definition} functions.typing
:lean: Functions/Typing:StatementTyped Functions/Typing:SequenceTyped
:uses: functions.calls functions.environments shared.typing.expressions shared.typing.statements

Write \\(\Delta;F\vdash\Gamma\mathrel{\xrightarrow{t}}\Gamma'\\) for statement
typing. [Shared's argument judgment](shared-typing.md#claim-shared.typing.expressions)
\\(\Delta\vdash\Gamma;{\overline e}:{\overline T}\Rightarrow\Gamma_e\\)
checks arguments left to right and threads their effects through the environment.
The receiver, when present, is the first argument.

\\[
\frac{
 \begin{gathered}
 (a,(\sigma,B))\in F \quad d\notin\operatorname{dom}(\Gamma) \\
 \Delta\vdash\Gamma;{\overline e}:\operatorname{params}(\sigma)\Rightarrow\Gamma_e
 \quad
 \Delta\vdash\Gamma_e;d:\operatorname{result}(\sigma)\Rightarrow\Gamma'
 \end{gathered}
}{\Delta;F\vdash\Gamma\mathrel{\xrightarrow{d:=\mathsf{call}\ a({\overline e})}}\Gamma'}
\\]

The freshness premise is vacuous when \\(d=\mathsf{none}\\). Arguments must
match the declared whole types; there is no automatic sharing at the boundary.
The rule consults [a signature](#claim-functions.signatures), not a body expansion.

Shared bindings and unpacking retain [their typing rule](shared-typing.md#claim-shared.typing.statements). Sequence typing chains
statement environments; an empty sequence requires a [well-formed environment](#claim-functions.environments):

\\[
\frac{\Delta\vdash\Gamma\mathrel{\xrightarrow{t}_{\mathrm{Shared}}}\Gamma'}
 {\Delta;F\vdash\Gamma\mathrel{\xrightarrow{t}}\Gamma'}
\qquad
\frac{\operatorname{WF}_{\Delta}(\Gamma)}
 {\Delta;F\vdash\Gamma\mathrel{\xrightarrow{[]}}\Gamma}
\qquad
\frac{\Delta;F\vdash\Gamma\mathrel{\xrightarrow{t}}\Gamma_1\quad
 \Delta;F\vdash\Gamma_1\mathrel{\xrightarrow{{\overline t}}}\Gamma'}
 {\Delta;F\vdash\Gamma\mathrel{\xrightarrow{t::{\overline t}}}\Gamma'}
\\]
```

```{definition} functions.result_typing
:lean: Functions/Typing:ResultTyped
:uses: functions.environments shared.typing.expressions

The judgment \\(\Delta\vdash\Gamma;r:R\Rightarrow_{\mathrm{return}}\Gamma'\\)
checks the final return. The [environment condition](#claim-functions.environments)
is inherited. It has two cases:

\\[
\frac{\operatorname{WF}_{\Delta}(\Gamma)}
 {\Delta\vdash\Gamma;\mathsf{none}:\mathsf{none}\Rightarrow_{\mathrm{return}}\Gamma}
\qquad
\frac{\Delta\vdash\Gamma;e:T\Rightarrow\Gamma'}
 {\Delta\vdash\Gamma;e:T\Rightarrow_{\mathrm{return}}\Gamma'}
\\]

The [expression judgment in the second rule is Shared's](shared-typing.md#claim-shared.typing.expressions).
```

```{definition} functions.bodies
:lean: Functions/Typing:BodyTyped
:uses: functions.typing functions.signatures functions.result_typing

A body checks against
[its signature](#claim-functions.signatures) by [typing its statements](#claim-functions.typing)
from the [parameter environment](#claim-functions.environments), then checking
its [return expression](#claim-functions.result_typing):

\\[
\frac{
 \Delta;F\vdash\operatorname{env}(\sigma)\mathrel{\xrightarrow{{\overline t}}}\Gamma_m
 \quad
 \Delta\vdash\Gamma_m;r:\operatorname{result}(\sigma)\Rightarrow_{\mathrm{return}}\Gamma_f
}{\Delta;F\vdash({\overline t};\mathsf{return}\ r):\sigma}
\\]

There is no consumption condition on \\(\Gamma_f\\) in this layer.
```

```{definition} functions.declaration_typing
:lean: Functions/Typing:DeclarationsTyped
:uses: functions.bodies functions.signatures

A declaration table checks when callable names are distinct and every [signature](#claim-functions.signatures)
is well formed and every [body checks against its signature](#claim-functions.bodies), using the complete
table. This permits mutual recursion.
```

```{definition} functions.program_typing
:lean: Functions/Typing:ProgramTyped
:uses: functions.declaration_typing functions.typing shared.typing.well_formed_classes

A program checks when its [nominal table](shared-typing.md#claim-shared.typing.well_formed_classes)
and [declaration table](#claim-functions.declaration_typing) check, and its [top-level statements check](#claim-functions.typing) from the empty
environment to some final environment.
```

```{theorem} functions.call_arity
:lean: Functions/Typing:call_arity
:uses: functions.typing

Every [typed call](#claim-functions.typing) names a declaration in its table, supplies exactly as many
arguments as that declaration has [parameters](#claim-functions.signatures), and supplies a destination
exactly when the declaration has a result.
```

````{example} functions.example.rejection
:lean: Functions/Checks:rejection
:uses: functions.signatures functions.typing

The [formal checks](#claim-functions.typing) reject each of these boundaries:

| Attempt | Reason |
| --- | --- |
| `fn bad(x: shared Token)` with class `Token` | Classes cannot be shared. |
| A `Point` method with a receiver of nominal type `Token` in the core [signature](#claim-functions.signatures) | A method's receiver must have its enclosing nominal type. |
| `let x = identity();` | The owned parameter is missing. |
| `identity(new Token());` | The call omits the destination for its result. |
````

## Stores, frames, and calls

```{definition} functions.machine
:lean: Functions/Step:Store Functions/Step:Frame Functions/Step:Configuration Functions/Step:Configuration.running Functions/Step:Configuration.initial
:uses: functions.calls shared.state

Each call has a *frame* \\(\phi\\) containing its local store \\(V\\), [remaining
body](#claim-functions.calls) \\(B\\), and destination \\(d\\) for its result in the caller. A store maps
local names to references or empty slots. The frame stack \\(K\\) lists the
active frame first, followed by suspended callers. The heap \\(H\\) and next
object identifier \\(n\\) belong to the whole machine:

\\[
\phi=(V,B,d),\qquad K=[\phi_0,\ldots,\phi_j],\qquad
M=\langle H,n,K\rangle.
\\]

Only the active frame's locals are accessible to expressions. For evaluation,
combine them with the heap and counter to form [Shared's state](shared.md#claim-shared.state) \\(S=(H,V,n)\\).
The Lean helper `Configuration.running` constructs a configuration from such a
state, an active body, a caller stack, and a result destination.

The initial configuration has an empty heap, counter zero, and **one frame**:
empty locals, the program's statements, no return expression, and no destination.
```

```{definition} functions.machine_finished
:lean: Functions/Step:Configuration.finished
:uses: functions.machine

A [configuration](#claim-functions.machine) is *finished* exactly when its frame stack is empty. Exhausting
the initial body's statements still leaves its frame to be popped.
```

```{definition} functions.roots
:lean: Functions/Step:Configuration.rootState Functions/Step:Configuration.roots
:uses: functions.machine shared.live

*Roots* are initialized local slots in **all live [frames](#claim-functions.machine)**, including suspended
callers. `rootState` concatenates their stores solely to reuse Shared's
[reachability relation](shared.md#claim-shared.live); identical local names in different frames remain distinct
slots. There are no retained stores from completed calls.
```

```{definition} functions.gc
:lean: Functions/Step:Configuration.collect Shared/Frames:State.collect
:uses: functions.machine shared.gc shared.well_formed shared.liveness

[As in Shared](shared.md#claim-shared.gc), *eager garbage collection*, written \\(\operatorname{gc}(M)\\), retains exactly
the heap entries reachable from the [live frames' roots](#claim-functions.roots). Here \\(o\\) is an
object identifier and \\(h\\) its class tag and field store. Reachability follows
zero or more initialized object fields, regardless of reference permission.
Write \\(\operatorname{live}_M(o)\\) for [Shared's `Live` relation](shared.md#claim-shared.live) with all frame
stores as its variable store. Then:

\\[
\operatorname{gc}(\langle H,n,K\rangle)
=\langle [(o,h)\in H\mid\operatorname{live}_M(o)],n,K\rangle.
\\]

Collection preserves surviving objects, their identifiers and fields, the
allocation counter, and every frame. It invokes no destructor. With no frames,
there are no roots and collection removes the entire heap.

This is a mathematical definition of the resulting heap. Its Lean definition
reuses Shared's noncomputable reachability filter; it does not prescribe an executable
graph-traversal algorithm.
```

```{definition} functions.parameters
:lean: Functions/Step:parameterStore Functions/Step:DestinationMatches
:uses: functions.machine functions.signatures

For equally long [parameter](#claim-functions.signatures) and reference lists, \\(\operatorname{bind}(\sigma,
{\overline v})\\) pairs each parameter name with its argument reference, in
order. Here \\(v\\) denotes a [runtime reference](shared.md#claim-shared.references). The call rule checks lengths
before using this operation.

\\[
\operatorname{bind}((x_1:T_1,\ldots,x_j:T_j)\,R,[v_1,\ldots,v_j])
=[x_1\mapsto v_1,\ldots,x_j\mapsto v_j].
\\]

Write \\(d\sim R\\) when [destination and result](#claim-functions.calls) are either both present or both
absent. This is an operational shape check, not runtime type checking.
```

```{definition} functions.return
:lean: Functions/Step:ResultEval Functions/Step:Deliver
:uses: functions.machine shared.give

Let \\(u\\) be an [optional reference](shared.md#claim-shared.references). Write \\(S\vdash r\Downarrow S_e;u\\)
for optional-result evaluation. An absent expression produces no reference and
leaves the state unchanged; a present one uses [Shared's value evaluation](shared.md#claim-shared.evaluation).

Delivery, written \\(V;d;u\Rightarrow V'\\), has just two cases:

\\[
V;\mathsf{none};\mathsf{none}\Rightarrow V
\qquad
\frac{x\notin\operatorname{dom}(V)}{V;x;v\Rightarrow(x\mapsto v)::V}.
\\]

```

```{definition} functions.execution
:lean: Functions/Step:RawStep Functions/Step:Step
:uses: functions.parameters functions.machine functions.return functions.gc shared.steps

Every transition first performs a *raw step* \\(M\rightsquigarrow M_r\\), then
[collects](#claim-functions.gc). Raw steps are auxiliary rules, not observable machine steps:

\\[
\frac{M\rightsquigarrow M_r}{M\longrightarrow\operatorname{gc}(M_r)}.
\\]

In the rules below, \\(S=(H,V,n)\\) is the [active frame's evaluation state](#claim-functions.machine),
and \\(S_e=(H_e,V_e,n_e)\\) is its result. Write
\\(S\vdash{\overline e}\Downarrow S_e;{\overline v}\\) for [Shared's
left-to-right argument evaluation](shared.md#claim-shared.evaluation), and \\(S\vdash t\Downarrow S_e\\) for one
[Shared binding or unpacking statement](shared-typing.md#claim-shared.typing.steps). Write \\(B_r=({\overline t};\mathsf{return}\ r)\\)
for the [remaining body](#claim-functions.calls) and \\(d_0\\) for the current frame's own return destination.

**Local statement**

\\[
\frac{S\vdash t\Downarrow S_e}
 {\langle H,n,(V,(t::{\overline t};\mathsf{return}\ r),d_0)::K\rangle
 \rightsquigarrow\langle H_e,n_e,(V_e,B_r,d_0)::K\rangle}
\\]

**Call**

\\[
\frac{
 \begin{gathered}
 (a,(\sigma,B_c))\in F\quad d\sim\operatorname{result}(\sigma)\quad
 d\notin\operatorname{dom}(V) \\
 S\vdash{\overline e}\Downarrow S_e;{\overline v}\quad
 |{\overline v}|=|\operatorname{params}(\sigma)|
 \end{gathered}
}{
 \begin{gathered}
 \langle H,n,(V,(d:=\mathsf{call}\ a({\overline e})::{\overline t};\mathsf{return}\ r),d_0)::K\rangle \\
 \rightsquigarrow
 \langle H_e,n_e,(\operatorname{bind}(\sigma,{\overline v}),B_c,d)::(V_e,B_r,d_0)::K\rangle
 \end{gathered}
}
\\]

Freshness is vacuous for an absent destination. The caller retains its updated
locals and continuation; the callee receives a new frame. Arguments are
transferred to parameters before collection. Qualified methods use this same rule.

**Return**

\\[
\frac{S\vdash r\Downarrow S_e;u\quad V_c;d;u\Rightarrow V'}
 {\langle H,n,(V,([];\mathsf{return}\ r),d)::(V_c,B_c,d_c)::K\rangle
 \rightsquigarrow\langle H_e,n_e,(V',B_c,d_c)::K\rangle}.
\\]

Evaluate the result, deliver it to the caller, and pop the callee. Collection
then uses the resumed caller and remaining frames as roots. A returned object
survives even when its last callee reference has just disappeared. Other objects
reachable only from the departed frame are reclaimed.

**Initial frame exit**

\\[
\langle H,n,[(V,([];\mathsf{return}\ \mathsf{none}),\mathsf{none})]\rangle
\rightsquigarrow\langle H,n,[]\rangle.
\\]

Collection makes this step's target \\(\langle\varnothing,n,[]\rangle\\).
Even an empty program takes this exit step. No rule steps from an empty stack.

No collection occurs midway through expression evaluation: constructor
arguments, call arguments, and returned values remain available until the raw
transition finishes transferring them. Collection runs after local statements,
calls, returns, and initial-frame exit.
```

````{example} functions.example.nested
:lean: Functions/Checks:nested
:uses: functions.return functions.execution

A [nested call](#claim-functions.execution) suspends the current function just as the outer call suspended
the program. Reusing a local name in different frames does not identify their
storage slots:

```dada
class Token {}
fn identity(token: → Token) → Token {
    return token→;
}
fn relay(token: → Token) → Token {
    let answer = identity(token→);
    return answer→;
}

let token = new Token();
let result = relay(token→);
```

All three frames have a local named `token`. [After both returns](#claim-functions.return), the program's
`token` is empty and `result` owns the original object. Only the initial
frame remains. The example [checks typing](#claim-functions.program_typing), these observations after the calls,
and the final exit step that pops this frame and empties the heap.
````

## Completion and recursion

````{example} functions.example.completion
:lean: Functions/Checks:completion
:uses: functions.bodies functions.return

This layer [accepts a function](#claim-functions.bodies) that leaves its owned parameter initialized:

```dada
class Token {}
fn leave(token: → Token) { }

let t = new Token();
leave(t→);
```

Returning from `leave` [pops its frame](#claim-functions.execution). The caller's `t` is empty, so [eager GC](#claim-functions.gc)
immediately reclaims the token, before the initial frame exits. Nothing invokes
a destructor. [Explicit unpacking](shared-typing.md#claim-shared.typing.bindings) is also accepted:

```dada
fn consume(token: → Token) {
    let Token → {} = token→;
}
```

The checks cover the first program's typing and full execution, and the second
function's body typing. Mandatory consumption is added in the next layer;
it is not a premise of these Functions rules.
````

```{definition} functions.traces
:lean: Functions/Step:Steps
:uses: functions.execution functions.return

The relation \\(M\longrightarrow^{*}M'\\) is the reflexive, transitive closure
[of steps](#claim-functions.execution), represented by zero steps or one step followed by a trace.
```

```{definition} functions.stuck
:lean: Functions/Step:Stuck
:uses: functions.machine_finished functions.execution

A [configuration](#claim-functions.machine) is *stuck* when it is not [finished](#claim-functions.machine_finished) and has no [successor](#claim-functions.execution).
```

````{example} functions.example.recursion
:lean: Functions/Checks:recursion
:uses: functions.traces functions.bodies

```dada
fn recur() {
    recur();
}
recur();
```

This [program checks](#claim-functions.program_typing). After any number of calls it can call again, adding one
suspended caller. The formal example supplies an infinite [sequence of adjacent
steps](#claim-functions.traces), all reachable from the initial configuration and none finished. The
[Shared completion bound](shared-typing.md#claim-shared.typing.safety) therefore does not extend to Functions.
````

```{theorem} functions.finished
:lean: Functions/Step:finished_no_step
:uses: functions.machine functions.execution

A [finished configuration](#claim-functions.machine_finished) has no [successor](#claim-functions.execution), for any declaration table.
```

```{theorem} functions.terminal_heap
:lean: Functions/Step:terminal_heap_empty
:uses: functions.execution functions.gc functions.machine

If a [machine step](#claim-functions.execution) reaches a [finished configuration](#claim-functions.machine_finished), its heap is empty.
The allocation counter need not be zero. This theorem concerns the targets of
steps; an arbitrary hand-written configuration with no frames need not already
have been [collected](#claim-functions.gc).
```

```{theorem} functions.shared_correspondence
:lean: Correspondence/SharedFunctionsFrames:framed_step_correspondence
:uses: functions.execution functions.machine shared.machine shared.steps

Embed a [Shared program configuration](shared.md#claim-shared.machine) with the same heap and allocation counter.
Its live frame becomes a one-element [Functions stack](#claim-functions.machine) with no result or return
destination; its absent frame becomes an empty stack. Wrap each statement as a
local statement.

Under any callable table, every [Shared step](shared.md#claim-shared.steps) has its corresponding [Functions
step](#claim-functions.execution). Conversely, every Functions successor of an embedded configuration is
exactly the embedding of a Shared successor. This includes collection and the
initial-frame exit, and quantifies over arbitrary successors and starting states.
There is no extra Functions-only completion step: both layers pop their initial
frame and collect at the same boundary.
```

```{theorem} functions.shared_traces
:lean: Correspondence/SharedFunctionsFrames:framed_steps_backward
:uses: functions.shared_correspondence functions.traces

Every finite [Functions trace](#claim-functions.traces) from an [embedded Shared program configuration](#claim-functions.shared_correspondence) has
a [Shared trace](shared.md#claim-shared.executions) to a configuration whose embedding is exactly the Functions
endpoint. This includes finished configurations with no frames or heap objects;
no well-formedness restriction is needed for this correspondence.
```

```{theorem} functions.shared_typing
:lean: Correspondence/SharedFunctions:typing_correspondence
:uses: functions.typing

For any initial and final [environments](shared-typing.md#claim-shared.typing.environments), nominal table, and callable table, a
sequence containing only embedded Shared statements [checks in Functions](#claim-functions.typing) if
and only if the original sequence [checks in Shared](shared-typing.md#claim-shared.typing.sequences).
```

```{theorem} functions.shared_finished
:lean: Correspondence/SharedFunctionsFrames:framed_finished_correspondence
:uses: functions.machine functions.shared_correspondence

A [Shared program configuration](shared.md#claim-shared.machine) is [finished](shared.md#claim-shared.finished) exactly when its [Functions embedding](#claim-functions.shared_correspondence)
is finished. Both conditions mean the initial frame has been popped.
```

```{theorem} functions.shared_stuck
:lean: Correspondence/SharedFunctionsFrames:framed_stuck_correspondence
:uses: functions.traces functions.shared_correspondence

A Shared program configuration is [stuck](shared.md#claim-shared.stuck) exactly when its [Functions embedding](#claim-functions.shared_correspondence)
[is stuck](#claim-functions.stuck), for any nominal and callable tables. An exhausted live frame can take
its exit step in both layers; an absent frame is finished in both.
```

## Safety across calls

````{example} functions.example.stack_safety
:lean: Functions/SafetyChecks:nested_safety
:uses: functions.example.nested

The [nested `relay`/`identity` example](#claim-functions.example.nested) uses `token` in three different frames.
The safety check now covers **every [finite execution prefix](#claim-functions.traces)** of that program:
the whole stack remains well typed, and execution cannot get stuck. It also
checks the returned initial frame and the empty terminal state after its exit.
The following [stack-typing definition](#claim-functions.stack_typing) explains what being well typed means for a suspended
caller whose result has not arrived yet.
````

```{definition} functions.frame_slots
:lean: Functions/Realization:Slots
:uses: functions.machine functions.environments shared.typing.realization

A *typed store* pairs a [frame's environment](#claim-functions.environments) with its [runtime locals](#claim-functions.machine), in order.
Their names agree, empty descriptions have empty slots, and each initialized
slot pairs a reference with its type. Write \\(\mathcal R\\) for the resulting
list of [reference/type pairs](shared-typing.md#claim-shared.typing.realization). These are the frame's *typed roots*.

The list retains occurrences: two shared aliases contribute two roots even
when their references are equal. This relation only pairs names, slots, and types; it does not itself require
distinct names or check the heap.
```

```{definition} functions.stack_typing
:lean: Functions/StackTyping:BodyFrom Functions/StackTyping:ContinuationTyped Functions/StackTyping:StackShape Functions/StackTyping:ConfigurationTyped Functions/Realization:heapState
:uses: functions.frame_slots functions.bodies functions.environments functions.machine shared.typing.realization

Write \\(\Delta;F\vdash M\ \mathsf{ok}\\) when the machine is *well typed*.
Its [nominal](shared-typing.md#claim-shared.typing.well_formed_classes) and [callable tables must check](#claim-functions.declaration_typing). The remaining requirements are:

| Component | Requirement |
| --- | --- |
| Active frame | Its locals form a typed store; its remaining statements and return expression check from that [environment](#claim-functions.environments) to its promised optional result type. |
| Suspended caller | Its stored locals form a typed store **before delivery**. The [delivery typing judgment](#claim-functions.destination_typing) checks the destination against the callee's promised result type. Its remaining body checks from the environment **after delivery**. |
| Outer callers | The same condition repeats down the stack, using each caller's own result destination and promised result type. |
| Initial frame | Its result and destination are absent; there is no caller below it. |
| Common heap | [Shared realization](shared-typing.md#claim-shared.typing.realization) holds with an empty variable environment and all frames' [typed roots](#claim-functions.frame_slots) as pending values. |

Thus the heap counts every owner, including those in suspended callers, while
expression evaluation sees only the active frame's locals. Realization checks
reference modes and views, nominal field types, object layouts, allocation
bounds, and compatibility of owning occurrences. A finished stack has no roots.

The Lean `BodyFrom` judgment checks a remaining body from a given environment.
`ContinuationTyped` checks the suspended callers, `StackShape` adds the active
frame (or an empty stack), and `ConfigurationTyped` joins those checks to heap
realization. None assumes a future execution or successful runtime operation.
```

```{theorem} functions.progress
:lean: Functions/Safety:ConfigurationTyped.progress
:uses: functions.stack_typing functions.execution

A [well-typed](#claim-functions.stack_typing) machine is [finished](#claim-functions.machine_finished) or has a [successor](#claim-functions.execution):

\\[
\Delta;F\vdash M\ \mathsf{ok}
\quad\Longrightarrow\quad
\mathsf{Finished}(M)\ \lor\ \exists M'.\ M\longrightarrow M'.
\\]

This includes calls, returns, and the initial-frame exit. The transition uses
the erased nominal table and the same callable table as the typing judgment.
```

```{theorem} functions.preservation
:lean: Functions/Safety:ConfigurationTyped.preservation
:uses: functions.stack_typing functions.execution functions.gc

Every machine [step](#claim-functions.execution) preserves [machine typing](#claim-functions.stack_typing):

\\[
\frac{\Delta;F\vdash M\ \mathsf{ok}\qquad M\longrightarrow M'}
 {\Delta;F\vdash M'\ \mathsf{ok}}.
\\]

This quantifies over every operational successor. Calls transfer argument roots
to a new frame; returns deliver the result and remove the callee. Eager
collection is part of the step. Objects reachable only from discarded locals
can disappear, while the returned value and surviving callers retain their
views and ownership guarantees.
```

```{theorem} functions.stack_ownership
:lean: Functions/Safety:ConfigurationTyped.ownership
:uses: functions.stack_typing functions.machine shared.well_formed

In a [well-typed](#claim-functions.stack_typing) machine, the references in all live frame slots and object
fields are pairwise compatible. Distinct [owning occurrences](shared.md#claim-shared.well_formed) can target the
same object only when both are shared. Every referenced object is allocated,
and every allocated object has an incoming reference from a frame or field.
These statements count all frames without requiring their local names to be
globally distinct.
```

```{theorem} functions.typed_completion
:lean: Functions/Safety:ConfigurationTyped.finished_heap_empty
:uses: functions.stack_typing functions.machine functions.gc

A [well-typed](#claim-functions.stack_typing) [finished](#claim-functions.machine_finished) configuration has an empty heap. Its initial frame has
been popped, so no locals remain. The allocation counter is retained.
This strengthens the earlier [step-target result](#claim-functions.terminal_heap) to every configuration
satisfying the stack typing judgment.
```

```{theorem} functions.safety
:lean: Functions/Safety:program_safety
:uses: functions.bodies functions.stack_typing functions.progress functions.preservation functions.traces

For a [well-typed program](#claim-functions.program_typing), every configuration reached by a [finite execution](#claim-functions.traces)
from its [initial configuration](#claim-functions.machine) remains [well typed](#claim-functions.stack_typing) and is [finished](#claim-functions.machine_finished) or can [step](#claim-functions.execution).
Consequently no such execution reaches a [stuck](#claim-functions.stuck) configuration.

The theorem permits recursion and does not assert termination or a step bound.
It starts from ordinary program typing; there is no operational-success
premise added to function or method declarations.
```

````{example} functions.example.recursive_safety
:lean: Functions/SafetyChecks:recursion_safety
:uses: functions.example.recursion functions.safety

For the earlier `recur()` program, the machine remains [well typed](#claim-functions.stack_typing) and is not
[stuck](#claim-functions.stuck) at every recursion depth. Each such state takes the next [recursive](#claim-functions.example.recursion)-call
step. Safety therefore holds along the infinite execution already exhibited
by the example, despite the growing stack.
````

## Later permissions and defaults

````{future-note} functions.future_permissions

The intended permission design has two independent distinctions:

| | Unique | Shared |
| --- | --- | --- |
| Owned | `given`, spelled `→` in signatures | `shared[]`, abbreviated `shared` |
| Leased | `mut[places...]` | `shared[places...]` |

The eventual mutable access expression is `p!`, including `p!method(...)`.
A bare place expression `p` will abbreviate `p.share`, producing
`shared[p]`; `p.method(...)` will use that borrowed receiver. Applying `share`
to a value, as in `p→share`, instead produces owned `shared[]` access.

Receiver declarations keep permissions in prefix position:

```dada
fn method(→self, arg: → Foo)
fn method(!self, arg: !Foo)
fn method(shared self, arg: shared Foo)
fn method(self, arg: Foo)
fn method[perm P](P self, arg: P Foo)
```

Bare argument types and bare `self` are intended to introduce generic
permissions constrained to support reading, rather than assume unique
ownership. The constraint's name and exact meaning remain to be designed;
`readable(P)` is a candidate, not an established predicate. These defaults,
leases, permission parameters, where-clauses, and permission-based method
overloading are outside the initial Functions layer.
````

## Appendix: inherited Shared machinery

```{definition} functions.inherited
:lean: Shared/Syntax:Value Shared/State:State Shared/Step:Give Shared/Step:Eval Shared/Step:EvalArgs Shared/Unpacking:Pattern Shared/Unpacking:Bind Shared/Typing:ExprTyped Shared/Typing:ArgsTyped
:uses: shared.declarations shared.struct shared.state shared.give shared.typing.types shared.typing.expressions shared.typing.patterns

The call machine and its typing judgments live in `Functions/`. They explicitly
use Shared's call-free expressions, storage, and binding judgments. There is
no change to those definitions in this layer:

| Machinery | Inherited behavior |
| --- | --- |
| [Nominal kinds](shared.md#claim-shared.declarations) | Classes cannot be shared; struct fields have struct types. |
| [Storage](shared.md#claim-shared.state) | References carry modes; slots hold a reference or are empty; allocation is monotonic. |
| [Views](shared-typing.md#claim-shared.typing.types) | Positive entries expose whole subtrees, negative entries record empty slots, and omissions are unknown. |
| [Giving](shared.md#claim-shared.give) | Unique access moves; shared access copies, promoting a unique final stored reference when necessary. |
| [Expressions](shared-typing.md#claim-shared.typing.expressions) | Constructor arguments are evaluated left to right and require whole declared types. Shared structs construct shared references immediately. |
| [Unpacking](shared-typing.md#claim-shared.typing.patterns) | Unpacking requires unique access and known status for every direct field, removes the container, and transfers its field slots to fresh bindings. |

The call syntax, frame stores, and call/return judgments are defined separately
in Functions. Assignments, destructors, branches, loops, and borrowing remain
outside this layer.
```
