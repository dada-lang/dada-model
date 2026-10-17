# Ownership views

The underlying state gives owned, showned, and shlease references object targets.
Unique leases target unique edges directly. A later ownership view may also draw
shleases joining an owning edge when its assumptions justify that view.

That second picture is a derived account whose assumptions require justification.
Unique ownership can identify one owning edge, while shared ownership may have
several independent owners. Unique-lease chains are already part of the state, rather than reconstructed
from object targets.

For example, the [shared-ownership execution](examples.md#a-shared-lease-survives-a-change-of-ownership)
allows a shlease to survive loss of one of several showned handles. A diagram
must not falsely imply that this shlease requires that particular handle to
remain present.

Graph facts should describe semantic state independently of layout hints. Frame
boxes, object boxes, and edge styles render those facts. A junction must have an
explicit meaning rather than quietly add provenance absent from the model.

The current diagram renderer draws explicit object-target and lease edge-target facts. Its general
obligations are stated in {anchor-ref}`meta.rendering.faithfulness`.
The mathematical relationship between these heap views remains a question for
the heap model itself.
