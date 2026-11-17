set_option maxHeartbeats 0 in
theorem igusaAlg3 : IgusaAlg 3 := by
  intro u
  rw [evenChars_val, Multiset.map_coe, esymm_coe]
  simp only [psi4T, chi10T, psi6T, chi12T, igusaP, sum_evenChars, prod_evenChars, List.map, esymmL]
  simp only [Sq0, Sq1, Sq2, Sq3, Sq4, Sq5, Sq6, Sq7, Sq8, Sq9]
  generalize u ![0, 0] = x0
  generalize u ![0, 1] = x1
  generalize u ![1, 0] = x2
  generalize u ![1, 1] = x3
  ring

