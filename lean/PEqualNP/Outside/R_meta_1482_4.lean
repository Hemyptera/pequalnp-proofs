import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1482_4
    (h1 : ¬ ∃ C : Circuit, C.size ≤ 64 ∧ IsAO2 26 C ∧
        circuitFun 26 C = graphFun (SimpleGraph.fromRel (fun a b : Fin 26 =>
          a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) ∅ ∧
        ∃ i j : ℕ, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧
          BelowF (SimpleGraph.fromRel (fun a b : Fin 26 =>
            a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone 26 C i j ∧
          (26 + j = C.output ∨ InCone 26 C j (C.output - 26)))
    (h2 : ¬ ∃ C : Circuit, C.size ≤ 64 ∧ IsAO2 26 C ∧
        circuitFun 26 C = graphFun (SimpleGraph.fromRel (fun a b : Fin 26 =>
          a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) ∅ ∧
        ∃ i j : ℕ, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧
          ¬ BelowF (SimpleGraph.fromRel (fun a b : Fin 26 =>
            a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone 26 C i j ∧
          (26 + j = C.output ∨ InCone 26 C j (C.output - 26))) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  classical
  let G : SimpleGraph (Fin 26) := SimpleGraph.fromRel (fun a b : Fin 26 =>
    a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 13 - (b.val - 13)) % 13 ∈ ([0, 1, 3, 9] : List ℕ))
  rintro ⟨C, hsz, hstruct, hfun, p, l, hpl, ⟨v, hv_init, hv_gate, hv_out⟩, _⟩
  have hgateAt : ∀ j, gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ => rfl
  have hgraphFun : ∀ x, graphFun G ∅ x =
      (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) := fun _ => rfl
  have hconeStep : ∀ cs g, coneStep 26 cs g =
      cs ++ [(g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => (w - 26) :: cs.getD (w - 26) [])] := fun _ _ => rfl
  have evalAnd : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have evalOr : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) :=
    fun a b => by cases a <;> cases b <;> rfl
  have hAO : IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      exact (hstruct j _ (List.getElem?_eq_getElem hj)).1
    · intro j hj w hw
      have hga : gateAt C j = C.gates[j] := by
        simp [hgateAt, List.getD_eq_getElem?_getD, hj]
      rw [hga] at hw
      obtain ⟨a, b, hin, _, ha, hb⟩ := (hstruct j _ (List.getElem?_eq_getElem hj)).2
      rw [hin] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      obtain ⟨a, b, hin, _, _, _⟩ := (hstruct j _ (List.getElem?_eq_getElem hj)).2
      simp [hin]
  have hinc_iff : ∀ u t : Fin 13,
      (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ↔
        (u.val + 13 - t.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
    decide
  have hcf : circuitFun 26 C = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔ graphFun G ∅ x = true
    rw [hfun x]
    rw [hgraphFun]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨u, t, hut, hxu, hxt⟩
      refine ⟨Fin.castAdd 13 u, Fin.natAdd 13 t, ?_, hxu, hxt⟩
      rw [SimpleGraph.fromRel_adj]
      refine ⟨by intro he; have := congrArg Fin.val he; simp at this; omega, Or.inl ?_⟩
      simp only [Fin.val_castAdd, Fin.val_natAdd, u.isLt, true_and]
      refine ⟨by omega, ?_⟩
      have hsub : 13 + t.val - 13 = t.val := by omega
      rw [hsub]
      exact (hinc_iff u t).mp hut
    · rintro ⟨a, b, hab, hxa, hxb⟩
      rw [SimpleGraph.fromRel_adj] at hab
      rcases hab.2 with ⟨ha, hb, hr⟩ | ⟨hb, ha, hr⟩
      · refine ⟨⟨a.val, ha⟩, ⟨b.val - 13, by omega⟩, (hinc_iff _ _).mpr hr, ?_, ?_⟩
        · convert hxa using 2; ext; simp
        · convert hxb using 2; ext; simp; omega
      · refine ⟨⟨b.val, hb⟩, ⟨a.val - 13, by omega⟩, (hinc_iff _ _).mpr hr, ?_, ?_⟩
        · convert hxb using 2; ext; simp
        · convert hxa using 2; ext; simp; omega
  have hstep_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp; omega
  have hstep_keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
        w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]
  have hwire_in : ∀ (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26),
      (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    change (C.gates.foldl _ (List.ofFn x)).getD i false = x ⟨i, hi⟩
    rw [hstep_keep C.gates (List.ofFn x) i (by simpa using hi)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi), List.getElem_ofFn]
    rfl
  have hwire_big : ∀ (x : Fin 26 → Bool) (i : ℕ), 26 + C.gates.length ≤ i →
      (C.wires (List.ofFn x)).getD i false = false := by
    intro x i hi
    change (C.gates.foldl _ (List.ofFn x)).getD i false = false
    rw [List.getD_eq_default]
    rw [hstep_len]; simpa using hi
  have hwire_gate : ∀ (x : Fin 26 → Bool) (k : ℕ) (hk : k < C.gates.length) (g : Gate) (a b : ℕ),
      C.gates[k]? = some g → g.inputs = [a, b] → a < 26 + k → b < 26 + k →
      (C.wires (List.ofFn x)).getD (26 + k) false =
        g.op.eval [(C.wires (List.ofFn x)).getD a false, (C.wires (List.ofFn x)).getD b false] := by
    intro x k hk g a b hgk hin ha hb
    have hsplit : C.gates = C.gates.take k ++ g :: C.gates.drop (k + 1) := by
      have h1 := (List.take_append_drop k C.gates).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      have hgq : C.gates[k] = g := Option.some.inj (by rw [← List.getElem?_eq_getElem hk, hgk])
      rwa [hgq] at h1
    let pre := C.gates.take k
    let post := C.gates.drop (k + 1)
    let wpre := pre.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
    have hpre_len : wpre.length = 26 + k := by
      dsimp [wpre, pre]
      rw [hstep_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    have hw_eq : C.wires (List.ofFn x) =
        post.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (wpre ++ [g.op.eval (g.inputs.map fun i => wpre.getD i false)]) := by
      change C.gates.foldl _ (List.ofFn x) = _
      conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    have hget_lt : ∀ i < 26 + k, (C.wires (List.ofFn x)).getD i false = wpre.getD i false := by
      intro i hi
      rw [hw_eq, hstep_keep post _ i (by simp [hpre_len]; omega), List.getD_append _ _ _ _ (by omega)]
    rw [hget_lt a ha, hget_lt b hb]
    rw [hw_eq, hstep_keep post _ (26 + k) (by simp [hpre_len])]
    have : (wpre ++ [g.op.eval (g.inputs.map fun i => wpre.getD i false)]).getD wpre.length false =
        g.op.eval (g.inputs.map fun i => wpre.getD i false) := by simp
    rw [← hpre_len, this, hin]
    rfl
  have hcone_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep 26) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; simp
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      simp [hconeStep]; omega
  have hcone_keep : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (gs.foldl (coneStep 26) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      rw [List.foldl_cons, ih _ i (by simp [hconeStep]; omega)]
      simp only [hconeStep]
      exact List.getD_append _ _ _ _ hi
  have hcone_at : ∀ (k : ℕ) (hk : k < C.gates.length),
      (cones 26 C).getD k [] =
        ((C.gates[k].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap
          (fun w => (w - 26) :: (cones 26 C).getD (w - 26) [])) := by
    intro k hk
    have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
      have h1 := (List.take_append_drop k C.gates).symm
      rwa [List.drop_eq_getElem_cons hk] at h1
    let pre := C.gates.take k
    let post := C.gates.drop (k + 1)
    let cpre := pre.foldl (coneStep 26) []
    have hcpre_len : cpre.length = k := by
      dsimp [cpre, pre]
      rw [hcone_len, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    have hc_eq : cones 26 C = post.foldl (coneStep 26) (coneStep 26 cpre C.gates[k]) := by
      unfold cones
      conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    have hpre_get : ∀ i < k, (cones 26 C).getD i [] = cpre.getD i [] := by
      intro i hi
      rw [hc_eq, hcone_keep post _ i (by simp [hconeStep, hcpre_len]; omega)]
      simp only [hconeStep]
      exact List.getD_append _ _ _ _ (by omega)
    conv_lhs => rw [hc_eq]
    rw [hcone_keep post _ k (by simp [hconeStep, hcpre_len])]
    simp only [hconeStep]
    let rhs := (C.gates[k].inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cpre.length))).flatMap
      (fun w => (w - 26) :: cpre.getD (w - 26) [])
    have hlast : (cpre ++ [rhs]).getD k [] = rhs := by
      rw [← hcpre_len]; simp
    rw [hlast]
    dsimp only [rhs]
    rw [hcpre_len]
    apply List.flatMap_congr
    intro w hw
    have hw' := of_decide_eq_true (List.mem_filter.mp hw).2
    rw [hpre_get (w - 26) (by omega)]
  have hcone_direct : ∀ (k i : ℕ) (hk : k < C.gates.length), i < k → 26 + i ∈ C.gates[k].inputs →
      InCone 26 C i k := by
    intro k i hk hik hmem
    unfold InCone
    rw [hcone_at k hk, List.mem_flatMap]
    refine ⟨26 + i, List.mem_filter.mpr ⟨hmem, by simp [hik]⟩, ?_⟩
    simp
  have hcone_step_trans : ∀ (k j i : ℕ) (hk : k < C.gates.length), j < k → 26 + j ∈ C.gates[k].inputs →
      InCone 26 C i j → InCone 26 C i k := by
    intro k j i hk hjk hmem hij
    unfold InCone at hij ⊢
    rw [hcone_at k hk, List.mem_flatMap]
    refine ⟨26 + j, List.mem_filter.mpr ⟨hmem, by simp [hjk]⟩, ?_⟩
    exact List.mem_cons_of_mem _ (by rw [Nat.add_sub_cancel_left]; exact hij)
  have hcone_lt : ∀ (k i : ℕ), k < C.gates.length → InCone 26 C i k → i < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hk hik
      unfold InCone at hik
      rw [hcone_at k hk, List.mem_flatMap] at hik
      obtain ⟨w, hw, hiw⟩ := hik
      have hw' := of_decide_eq_true (List.mem_filter.mp hw).2
      simp only [List.mem_cons] at hiw
      rcases hiw with rfl | hsub
      · omega
      · have := ih (w - 26) (by omega) i (by omega) hsub
        omega
  have hcone_trans : ∀ (k j i : ℕ), k < C.gates.length → InCone 26 C i j → InCone 26 C j k →
      InCone 26 C i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro j i hk hij hjk
      unfold InCone at hjk
      rw [hcone_at k hk, List.mem_flatMap] at hjk
      obtain ⟨w, hw, hjw⟩ := hjk
      have hwin := (List.mem_filter.mp hw).1
      have hwb := of_decide_eq_true (List.mem_filter.mp hw).2
      have hw_eq : 26 + (w - 26) = w := by omega
      simp only [List.mem_cons] at hjw
      rcases hjw with rfl | hsub
      · exact hcone_step_trans k (w - 26) i hk (by omega) (by rwa [hw_eq]) hij
      · have him : InCone 26 C i (w - 26) := ih (w - 26) (by omega) j i (by omega) hij hsub
        exact hcone_step_trans k (w - 26) i hk (by omega) (by rwa [hw_eq]) him
  let ep : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p)
  let el : Fin 26 → Bool := fun i => decide (i = Fin.natAdd 13 l)
  let epl : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  have hep_out : (C.wires (List.ofFn ep)).getD C.output false = false := by
    cases h : C.eval (List.ofFn ep)
    · exact h
    · exfalso
      obtain ⟨u, t, _, _, hxt⟩ := (hfun ep).mp h
      simp only [ep, decide_eq_true_eq] at hxt
      have := congrArg Fin.val hxt
      simp at this; omega
  have hel_out : (C.wires (List.ofFn el)).getD C.output false = false := by
    cases h : C.eval (List.ofFn el)
    · exact h
    · exfalso
      obtain ⟨u, t, _, hxu, _⟩ := (hfun el).mp h
      simp only [el, decide_eq_true_eq] at hxu
      have := congrArg Fin.val hxu
      simp at this; omega
  have hepl_out : (C.wires (List.ofFn epl)).getD C.output false = true :=
    (hfun epl).mpr ⟨p, l, hpl, by simp [epl], by simp [epl]⟩
  have hout_ge : 26 ≤ C.output := by
    by_contra hlt
    push Not at hlt
    rw [hwire_in epl C.output hlt] at hepl_out
    simp only [epl, decide_eq_true_eq] at hepl_out
    rcases hepl_out with heq | heq
    · rw [hwire_in ep C.output hlt, heq] at hep_out
      simp [ep] at hep_out
    · rw [hwire_in el C.output hlt, heq] at hel_out
      simp [el] at hel_out
  have hout_lt : C.output < 26 + C.gates.length := by
    by_contra hge
    push Not at hge
    rw [hwire_big epl C.output hge] at hepl_out
    exact Bool.false_ne_true hepl_out
  let outG := C.output - 26
  have houtG_lt : outG < C.gates.length := by omega
  have houtG_eq : 26 + outG = C.output := by omega
  let ReachesOut : ℕ → Prop := fun u => u = outG ∨ InCone 26 C u outG
  have hP_ex : ∃ k : ℕ, k < C.gates.length ∧ ReachesOut k ∧
      (C.wires (List.ofFn epl)).getD (26 + k) false = true ∧
      (C.wires (List.ofFn ep)).getD (26 + k) false = false ∧
      v (26 + k) = false :=
    ⟨outG, houtG_lt, Or.inl rfl, by rwa [houtG_eq], by rwa [houtG_eq], by rwa [houtG_eq]⟩
  let k1 := Nat.find hP_ex
  have hk1_spec := Nat.find_spec hP_ex
  have hk1_lt : k1 < C.gates.length := hk1_spec.1
  have hk1_reach : ReachesOut k1 := hk1_spec.2.1
  have hk1_epl : (C.wires (List.ofFn epl)).getD (26 + k1) false = true := hk1_spec.2.2.1
  have hk1_ep : (C.wires (List.ofFn ep)).getD (26 + k1) false = false := hk1_spec.2.2.2.1
  have hk1_v : v (26 + k1) = false := hk1_spec.2.2.2.2
  have hk1_min : ∀ k' < k1, ReachesOut k' →
      (C.wires (List.ofFn epl)).getD (26 + k') false = true →
      (C.wires (List.ofFn ep)).getD (26 + k') false = false →
      v (26 + k') = false → False := by
    intro k' hk' hr h1' h2' h3'
    exact Nat.find_min hP_ex hk' ⟨by omega, hr, h1', h2', h3'⟩
  have hno_in_P : ∀ w < 26, (C.wires (List.ofFn epl)).getD w false = true →
      (C.wires (List.ofFn ep)).getD w false = false → v w = false → False := by
    intro w hw hwepl hwep hwv
    rw [hwire_in epl w hw] at hwepl
    rw [hwire_in ep w hw] at hwep
    simp only [epl, decide_eq_true_eq] at hwepl
    simp only [ep, decide_eq_false_iff_not] at hwep
    rcases hwepl with heq | heq
    · exact hwep heq
    · have hwval : w = 13 + l.val := by
        have := congrArg Fin.val heq
        simp only [Fin.val_natAdd] at this
        omega
      rw [hwval, (hv_init l).2] at hwv
      simp at hwv
  have hk1_some : C.gates[k1]? = some C.gates[k1] := List.getElem?_eq_getElem hk1_lt
  obtain ⟨hk1_op, c, d, hk1_in, _, hc_lt, hd_lt⟩ := hstruct k1 C.gates[k1] hk1_some
  have hreach_child : ∀ w, w ∈ C.gates[k1].inputs → 26 ≤ w → w < 26 + k1 → ReachesOut (w - 26) := by
    intro w hwin hw26 hwlt
    have hw_eq : 26 + (w - 26) = w := by omega
    have hdir : InCone 26 C (w - 26) k1 :=
      hcone_direct k1 (w - 26) hk1_lt (by omega) (by rwa [hw_eq])
    rcases hk1_reach with hk1_eq | hck
    · rw [hk1_eq] at hdir; exact Or.inr hdir
    · exact Or.inr (hcone_trans outG k1 (w - 26) houtG_lt hdir hck)
  have hnot_child_P : ∀ w, w ∈ C.gates[k1].inputs → w < 26 + k1 →
      (C.wires (List.ofFn epl)).getD w false = true →
      (C.wires (List.ofFn ep)).getD w false = false →
      v w = false → False := by
    intro w hwin hwlt hwepl hwep hwv
    by_cases hw26 : w < 26
    · exact hno_in_P w hw26 hwepl hwep hwv
    · have hw_eq : 26 + (w - 26) = w := by omega
      exact hk1_min (w - 26) (by omega) (hreach_child w hwin (by omega) hwlt)
        (by rwa [hw_eq]) (by rwa [hw_eq]) (by rwa [hw_eq])
  have hk1_and : C.gates[k1].op = GateOp.and := by
    rcases hk1_op with hand | hor
    · exact hand
    · exfalso
      have heval_epl := hwire_gate epl k1 hk1_lt C.gates[k1] c d hk1_some hk1_in hc_lt hd_lt
      have heval_ep := hwire_gate ep k1 hk1_lt C.gates[k1] c d hk1_some hk1_in hc_lt hd_lt
      have hv_or := (hv_gate k1 C.gates[k1] c d hk1_some hk1_in).2 hor
      rw [hk1_epl, hor] at heval_epl
      rw [hk1_ep, hor] at heval_ep
      rw [hk1_v] at hv_or
      rw [evalOr] at heval_epl heval_ep
      have ⟨hvc, hvd⟩ := Bool.or_eq_false_iff.mp hv_or.symm
      have ⟨hep_c, hep_d⟩ := Bool.or_eq_false_iff.mp heval_ep.symm
      rcases (Bool.or_eq_true _ _).mp heval_epl.symm with hce | hde
      · exact hnot_child_P c (by simp [hk1_in]) hc_lt hce hep_c hvc
      · exact hnot_child_P d (by simp [hk1_in]) hd_lt hde hep_d hvd
  have hk1_epl_eq := hwire_gate epl k1 hk1_lt C.gates[k1] c d hk1_some hk1_in hc_lt hd_lt
  have hk1_ep_eq := hwire_gate ep k1 hk1_lt C.gates[k1] c d hk1_some hk1_in hc_lt hd_lt
  have hk1_v_and := (hv_gate k1 C.gates[k1] c d hk1_some hk1_in).1 hk1_and
  rw [hk1_epl, hk1_and] at hk1_epl_eq
  rw [hk1_ep, hk1_and] at hk1_ep_eq
  rw [hk1_v] at hk1_v_and
  change false = (((C.wires (List.ofFn ep)).getD c false && v d) ||
    (v c && (C.wires (List.ofFn ep)).getD d false)) at hk1_v_and
  rw [evalAnd] at hk1_epl_eq hk1_ep_eq
  have ⟨hc_epl, hd_epl⟩ := (Bool.and_eq_true _ _).mp hk1_epl_eq.symm
  have hc_ep : (C.wires (List.ofFn ep)).getD c false = false := by
    cases hc : (C.wires (List.ofFn ep)).getD c false with
    | false => rfl
    | true =>
      exfalso
      rw [hc, Bool.true_and] at hk1_ep_eq hk1_v_and
      have hvd : v d = false := (Bool.or_eq_false_iff.mp hk1_v_and.symm).1
      exact hnot_child_P d (by simp [hk1_in]) hd_lt hd_epl hk1_ep_eq.symm hvd
  have hd_ep : (C.wires (List.ofFn ep)).getD d false = false := by
    cases hd : (C.wires (List.ofFn ep)).getD d false with
    | false => rfl
    | true =>
      exfalso
      rw [hd, Bool.and_true] at hk1_ep_eq hk1_v_and
      have hvc : v c = false := (Bool.or_eq_false_iff.mp hk1_v_and.symm).2
      exact hnot_child_P c (by simp [hk1_in]) hc_lt hc_epl hk1_ep_eq.symm hvc
  have hnest : ∃ i j : ℕ, i < C.gates.length ∧ j < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j ∧
      (26 + j = C.output ∨ InCone 26 C j (C.output - 26)) := by
    cases hk1_el : (C.wires (List.ofFn el)).getD (26 + k1) false with
    | true =>
      have hk1_ne_out : k1 ≠ outG := by
        intro hk1_eq
        rw [hk1_eq, houtG_eq, hel_out] at hk1_el
        exact Bool.false_ne_true hk1_el
      have hk1_in_out : InCone 26 C k1 outG := hk1_reach.resolve_left hk1_ne_out
      have hQ_ex : ∃ j : ℕ, j < C.gates.length ∧ InCone 26 C k1 j ∧ ReachesOut j ∧
          (C.wires (List.ofFn el)).getD (26 + j) false = false :=
        ⟨outG, houtG_lt, hk1_in_out, Or.inl rfl, by rwa [houtG_eq]⟩
      let j := Nat.find hQ_ex
      have hj_spec := Nat.find_spec hQ_ex
      have hj_lt : j < C.gates.length := hj_spec.1
      have hj_cone : InCone 26 C k1 j := hj_spec.2.1
      have hj_reach : ReachesOut j := hj_spec.2.2.1
      have hj_el : (C.wires (List.ofFn el)).getD (26 + j) false = false := hj_spec.2.2.2
      have hj_some : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj_lt
      obtain ⟨hj_op, a, b, hj_in, _, ha_lt, hb_lt⟩ := hstruct j C.gates[j] hj_some
      have hj_cone' := hj_cone
      unfold InCone at hj_cone'
      rw [hcone_at j hj_lt, List.mem_flatMap] at hj_cone'
      obtain ⟨w, hw, hkw⟩ := hj_cone'
      have hwin := (List.mem_filter.mp hw).1
      have hwb := of_decide_eq_true (List.mem_filter.mp hw).2
      have hw_el : (C.wires (List.ofFn el)).getD w false = true := by
        have hw_eq : 26 + (w - 26) = w := by omega
        simp only [List.mem_cons] at hkw
        rcases hkw with hwk | hwk
        · rw [← hw_eq, ← hwk]; exact hk1_el
        · cases h : (C.wires (List.ofFn el)).getD w false with
          | true => rfl
          | false =>
            exfalso
            have hdir_w : InCone 26 C (w - 26) j :=
              hcone_direct j (w - 26) hj_lt (by omega) (by rwa [hw_eq])
            have hreach_w : ReachesOut (w - 26) := by
              rcases hj_reach with hj_eq | hcj
              · rw [hj_eq] at hdir_w; exact Or.inr hdir_w
              · exact Or.inr (hcone_trans outG j (w - 26) houtG_lt hdir_w hcj)
            exact Nat.find_min hQ_ex (show w - 26 < j by omega)
              ⟨by omega, hwk, hreach_w, by rwa [hw_eq]⟩
      have hj_and : C.gates[j].op = GateOp.and := by
        rcases hj_op with hand | hor
        · exact hand
        · exfalso
          have hev := hwire_gate el j hj_lt C.gates[j] a b hj_some hj_in ha_lt hb_lt
          rw [hj_el, hor] at hev
          rw [evalOr] at hev
          rw [hj_in] at hwin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
          rcases hwin with rfl | rfl
          · rw [hw_el, Bool.true_or] at hev; exact Bool.false_ne_true hev
          · rw [hw_el, Bool.or_true] at hev; exact Bool.false_ne_true hev
      refine ⟨k1, j, hk1_lt, hj_lt, ?_, ?_, hj_cone, ?_⟩
      · simpa [hgateAt, List.getD_eq_getElem?_getD, hk1_lt] using hk1_and
      · simpa [hgateAt, List.getD_eq_getElem?_getD, hj_lt] using hj_and
      · rcases hj_reach with hj_eq | hcj
        · left; rw [hj_eq]; exact houtG_eq
        · right; exact hcj
    | false =>
      have hk1_el_eq := hwire_gate el k1 hk1_lt C.gates[k1] c d hk1_some hk1_in hc_lt hd_lt
      rw [hk1_el, hk1_and] at hk1_el_eq
      rw [evalAnd] at hk1_el_eq
      have hno_in_Q : ∀ w < 26, (C.wires (List.ofFn epl)).getD w false = true →
          (C.wires (List.ofFn ep)).getD w false = false →
          (C.wires (List.ofFn el)).getD w false = false → False := by
        intro w hw h1' h2' h3'
        rw [hwire_in epl w hw] at h1'
        rw [hwire_in ep w hw] at h2'
        rw [hwire_in el w hw] at h3'
        simp only [epl, decide_eq_true_eq] at h1'
        simp only [ep, el, decide_eq_false_iff_not] at h2' h3'
        rcases h1' with h1' | h1'
        · exact h2' h1'
        · exact h3' h1'
      have hchild_ex : ∃ w, w ∈ C.gates[k1].inputs ∧ w < 26 + k1 ∧
          (C.wires (List.ofFn epl)).getD w false = true ∧
          (C.wires (List.ofFn ep)).getD w false = false ∧
          (C.wires (List.ofFn el)).getD w false = false := by
        rcases Bool.and_eq_false_iff.mp hk1_el_eq.symm with hcel | hdel
        · exact ⟨c, by simp [hk1_in], hc_lt, hc_epl, hc_ep, hcel⟩
        · exact ⟨d, by simp [hk1_in], hd_lt, hd_epl, hd_ep, hdel⟩
      obtain ⟨w0, hw0_in, hw0_lt, hw0_epl, hw0_ep, hw0_el⟩ := hchild_ex
      have hw0_ge : 26 ≤ w0 := by
        by_contra hlt; push Not at hlt
        exact hno_in_Q w0 hlt hw0_epl hw0_ep hw0_el
      have hR_ex : ∃ i : ℕ, i < C.gates.length ∧ InCone 26 C i k1 ∧
          (C.wires (List.ofFn epl)).getD (26 + i) false = true ∧
          (C.wires (List.ofFn ep)).getD (26 + i) false = false ∧
          (C.wires (List.ofFn el)).getD (26 + i) false = false := by
        have hw_eq : 26 + (w0 - 26) = w0 := by omega
        exact ⟨w0 - 26, by omega,
          hcone_direct k1 (w0 - 26) hk1_lt (by omega) (by rwa [hw_eq]),
          by rwa [hw_eq], by rwa [hw_eq], by rwa [hw_eq]⟩
      let i := Nat.find hR_ex
      have hi_spec := Nat.find_spec hR_ex
      have hi_lt : i < C.gates.length := hi_spec.1
      have hi_cone : InCone 26 C i k1 := hi_spec.2.1
      have hi_epl : (C.wires (List.ofFn epl)).getD (26 + i) false = true := hi_spec.2.2.1
      have hi_ep : (C.wires (List.ofFn ep)).getD (26 + i) false = false := hi_spec.2.2.2.1
      have hi_el : (C.wires (List.ofFn el)).getD (26 + i) false = false := hi_spec.2.2.2.2
      have hi_some : C.gates[i]? = some C.gates[i] := List.getElem?_eq_getElem hi_lt
      obtain ⟨hi_op, a, b, hi_in, _, ha_lt, hb_lt⟩ := hstruct i C.gates[i] hi_some
      have hi_and : C.gates[i].op = GateOp.and := by
        rcases hi_op with hand | hor
        · exact hand
        · exfalso
          have hepl_i := hwire_gate epl i hi_lt C.gates[i] a b hi_some hi_in ha_lt hb_lt
          have hep_i := hwire_gate ep i hi_lt C.gates[i] a b hi_some hi_in ha_lt hb_lt
          have hel_i := hwire_gate el i hi_lt C.gates[i] a b hi_some hi_in ha_lt hb_lt
          rw [hi_epl, hor] at hepl_i
          rw [hi_ep, hor] at hep_i
          rw [hi_el, hor] at hel_i
          rw [evalOr] at hepl_i hep_i hel_i
          have ⟨hap, hbp⟩ := Bool.or_eq_false_iff.mp hep_i.symm
          have ⟨hal, hbl⟩ := Bool.or_eq_false_iff.mp hel_i.symm
          have hpick : ∃ w, w ∈ C.gates[i].inputs ∧ w < 26 + i ∧
              (C.wires (List.ofFn epl)).getD w false = true ∧
              (C.wires (List.ofFn ep)).getD w false = false ∧
              (C.wires (List.ofFn el)).getD w false = false := by
            rcases (Bool.or_eq_true _ _).mp hepl_i.symm with hae | hbe
            · exact ⟨a, by simp [hi_in], ha_lt, hae, hap, hal⟩
            · exact ⟨b, by simp [hi_in], hb_lt, hbe, hbp, hbl⟩
          obtain ⟨w, hwin, hwlt, h1', h2', h3'⟩ := hpick
          by_cases hw26 : w < 26
          · exact hno_in_Q w hw26 h1' h2' h3'
          · have hw_eq : 26 + (w - 26) = w := by omega
            have hdir : InCone 26 C (w - 26) i :=
              hcone_direct i (w - 26) hi_lt (by omega) (by rwa [hw_eq])
            have hck : InCone 26 C (w - 26) k1 := hcone_trans k1 i (w - 26) hk1_lt hdir hi_cone
            exact Nat.find_min hR_ex (show w - 26 < i by omega)
              ⟨by omega, hck, by rwa [hw_eq], by rwa [hw_eq], by rwa [hw_eq]⟩
      refine ⟨i, k1, hi_lt, hk1_lt, ?_, ?_, hi_cone, ?_⟩
      · simpa [hgateAt, List.getD_eq_getElem?_getD, hi_lt] using hi_and
      · simpa [hgateAt, List.getD_eq_getElem?_getD, hk1_lt] using hk1_and
      · rcases hk1_reach with hk1_eq | hck
        · left; rw [hk1_eq]; exact houtG_eq
        · right; exact hck
  obtain ⟨i, j, hi_lt, hj_lt, hi_and, hj_and, hij_cone, hj_live⟩ := hnest
  by_cases hbel : BelowF G C i
  · exact h1 ⟨C, hsz, hAO, hcf, i, j, hi_lt, hj_lt, hi_and, hbel, hj_and, hij_cone, hj_live⟩
  · exact h2 ⟨C, hsz, hAO, hcf, i, j, hi_lt, hj_lt, hi_and, hbel, hj_and, hij_cone, hj_live⟩
