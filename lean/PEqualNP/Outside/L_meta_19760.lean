import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19760
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [14, 18]⟩, ⟨GateOp.and, [0, 19]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [1, 21]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [23, 14]⟩, ⟨GateOp.and, [2, 24]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [26, 15]⟩, ⟨GateOp.and, [3, 27]⟩, ⟨GateOp.or, [13, 18]⟩, ⟨GateOp.and, [4, 29]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.and, [5, 31]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.and, [6, 33]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [7, 35]⟩, ⟨GateOp.or, [20, 22]⟩, ⟨GateOp.or, [37, 25]⟩, ⟨GateOp.or, [38, 28]⟩, ⟨GateOp.or, [39, 30]⟩, ⟨GateOp.or, [40, 32]⟩, ⟨GateOp.or, [41, 34]⟩, ⟨GateOp.or, [42, 36]⟩], 43⟩
theorem basis : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_19760

theorem PEqualNP.Outside.L_meta_19760 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5882310434002997580 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨PEqualNP.Outside.L_meta_19760.circ, PEqualNP.Outside.L_meta_19760.basis, by decide, PEqualNP.Outside.L_meta_19760.rep⟩

