import examples.German.draft.obligation

/-!
# German's protocol: coherence

The per-rule invariance proofs with their certificates linked in (completeness certified
by Maude in `obligation.lean`; soundness, and the disjointness `inv_bad`, still open).
-/

namespace German

open Expresso

#link sendReqS_inv
#link sendReqEI_inv
#link sendReqES_inv
#link recvReqS_inv
#link recvReqE_inv
#link sendInvE_inv
#link sendInvS_inv
#link sendInvAck_inv
#link recvInvAckS_inv
#link recvInvAckN_inv
#link sendGntSN_inv
#link sendGntSS_inv
#link sendGntE_inv
#link recvGntS_inv
#link recvGntE_inv

/-- The whole protocol preserves the invariant, certificates linked. -/
theorem german_inv_linked : isOverPost german inv inv :=
  isOverPost_choice sendReqS_inv.linked
    (isOverPost_choice sendReqEI_inv.linked
    (isOverPost_choice sendReqES_inv.linked
    (isOverPost_choice recvReqS_inv.linked
    (isOverPost_choice recvReqE_inv.linked
    (isOverPost_choice sendInvE_inv.linked
    (isOverPost_choice sendInvS_inv.linked
    (isOverPost_choice sendInvAck_inv.linked
    (isOverPost_choice recvInvAckS_inv.linked
    (isOverPost_choice recvInvAckN_inv.linked
    (isOverPost_choice sendGntSN_inv.linked
    (isOverPost_choice sendGntSS_inv.linked
    (isOverPost_choice sendGntE_inv.linked
    (isOverPost_choice recvGntS_inv.linked
    (recvGntE_inv.linked))))))))))))))

/-- Coherence: from an initial state, never an exclusive cache next to an exclusive or a
shared one. -/
theorem german_coherent_linked {x y : Conf} (hx : Pattern.holds [initP] x)
    (hxy : german.steps x y) : ¬ bad.holds y :=
  fun hy => inv_bad ⟨y, invariant init_inv german_inv_linked hx hxy, hy⟩

#print axioms german_coherent_linked

end German
