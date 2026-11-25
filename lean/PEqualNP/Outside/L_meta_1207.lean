import PEqualNP.Defs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds

/-- The ten-gate AND/OR circuit for the edge function of graph n8-058, from the step's sketch:
`8=OR(1,2) 9=AND(0,8) 10=OR(1,5) 11=AND(3,10) 12=OR(2,5) 13=AND(4,12) 14=AND(6,7)
15=OR(9,11) 16=OR(15,13) 17=OR(16,14)`. -/
theorem L_meta_1207 :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) =
          (fun x : Fin 8 → Bool =>
            (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) ||
            (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨⟨[
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.and, [0, 8]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.and, [3, 10]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.and, [4, 12]⟩,
      ⟨GateOp.and, [6, 7]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [15, 13]⟩,
      ⟨GateOp.or, [16, 14]⟩], 17⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by decide⟩
  · decide
  · decide

end PEqualNP.Outside
