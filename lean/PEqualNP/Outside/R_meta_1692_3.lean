import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_1692_3
    (hSingle : let E : List (ℕ × ℕ) := (List.finRange 13).flatMap fun p =>
        ((List.finRange 13).filter fun l => decide (p ∈ singerLines3 l)).map fun l => (p.val, 13 + l.val)
      ∀ C : Circuit,
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
        (∀ p l : Fin 13, p ∈ singerLines3 l →
          C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) →
        (∀ Q ∈ quadrangles singerLines3,
          C.eval (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
            List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))) = false) →
        IsSingleRead C 26 (fun i => decide (13 ≤ i)) E →
        64 ≤ C.size)
    (hDouble : let E : List (ℕ × ℕ) := (List.finRange 13).flatMap fun p =>
        ((List.finRange 13).filter fun l => decide (p ∈ singerLines3 l)).map fun l => (p.val, 13 + l.val)
      ∀ C : Circuit,
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
        (∀ p l : Fin 13, p ∈ singerLines3 l →
          C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) →
        (∀ Q ∈ quadrangles singerLines3,
          C.eval (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
            List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))) = false) →
        ¬ IsSingleRead C 26 (fun i => decide (13 ≤ i)) E →
        64 ≤ C.size) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  classical
  intro gates out hops hreads hpos hneg
  have evalAnd : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have evalOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hquadDef : quadrangles singerLines3 =
      (Finset.univ.powersetCard 4).filter fun Q => ∀ l : Fin 13, (Q ∩ singerLines3 l).card ≤ 2 := rfl
  have hmissDef : ∀ Q, missLines singerLines3 Q =
      Finset.univ.filter fun l => Disjoint (singerLines3 l) Q := fun _ => rfl
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hstep_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have hstep_keep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp [step]; omega)]
      simp only [step]
      exact List.getD_append _ _ _ _ hi
  have hwire_in : ∀ (gs : List Gate) (x : List Bool) (i : ℕ), i < x.length →
      (Circuit.wires ⟨gs, 0⟩ x).getD i false = x.getD i false := by
    intro gs x i hi
    exact hstep_keep gs x i hi
  have hwire_big : ∀ (gs : List Gate) (x : List Bool) (i : ℕ), x.length + gs.length ≤ i →
      (Circuit.wires ⟨gs, 0⟩ x).getD i false = false := by
    intro gs x i hi
    change (gs.foldl step x).getD i false = false
    rw [List.getD_eq_default]
    rw [hstep_len]; exact hi
  have hwire_gate : ∀ (gs : List Gate) (x : List Bool) (k : ℕ) (g : Gate),
      x.length = 26 → gs[k]? = some g → (∀ w ∈ g.inputs, w < 26 + k) →
      (Circuit.wires ⟨gs, 0⟩ x).getD (26 + k) false =
        g.op.eval (g.inputs.map fun w => (Circuit.wires ⟨gs, 0⟩ x).getD w false) := by
    intro gs x k g hx hgk hrb
    have hk : k < gs.length := (List.getElem?_eq_some_iff.mp hgk).1
    have hsplit : gs = gs.take k ++ g :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      have hgq : gs[k] = g := Option.some.inj (by rw [← List.getElem?_eq_getElem hk, hgk])
      rwa [hgq] at h1
    let pre := gs.take k
    let post := gs.drop (k + 1)
    let wpre := pre.foldl step x
    have hpre_len : wpre.length = 26 + k := by
      dsimp [wpre, pre]
      rw [hstep_len, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    have hw_eq : Circuit.wires ⟨gs, 0⟩ x = post.foldl step (step wpre g) := by
      change gs.foldl step x = _
      conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    have hget_lt : ∀ i < 26 + k, (Circuit.wires ⟨gs, 0⟩ x).getD i false = wpre.getD i false := by
      intro i hi
      rw [hw_eq, hstep_keep post _ i (by simp [step, hpre_len]; omega)]
      simp only [step]
      exact List.getD_append _ _ _ _ (by omega)
    conv_lhs => rw [hw_eq]
    rw [hstep_keep post _ (26 + k) (by simp [step, hpre_len])]
    simp only [step]
    have hlast : (wpre ++ [g.op.eval (g.inputs.map fun i => wpre.getD i false)]).getD wpre.length false =
        g.op.eval (g.inputs.map fun i => wpre.getD i false) := by simp
    rw [← hpre_len, hlast]
    congr 1
    apply List.map_congr_left
    intro w hw
    exact (hget_lt w (hrb w hw)).symm
  let Valid (gs : List Gate) : Prop :=
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ w ∈ g.inputs, w < 26 + j)
  let Strict (gs : List Gate) : Prop :=
    ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j
  have helim_alias : ∀ (gs : List Gate) (out k a : ℕ), Valid gs →
      k < gs.length → out < 26 + gs.length → a < 26 + k →
      (∀ x : List Bool, x.length = 26 →
        (Circuit.wires ⟨gs, 0⟩ x).getD (26 + k) false = (Circuit.wires ⟨gs, 0⟩ x).getD a false) →
      ∃ (gs' : List Gate) (out' : ℕ), gs'.length + 1 = gs.length ∧ Valid gs' ∧
        ∀ x : List Bool, x.length = 26 →
          Circuit.eval ⟨gs', out'⟩ x = Circuit.eval ⟨gs, out⟩ x := by
    intro gs out k a hval hk hout ha halias
    let remap (w : ℕ) : ℕ := if w = 26 + k then a else if 26 + k < w then w - 1 else w
    let gs' : List Gate := gs.take k ++ (gs.drop (k + 1)).map (fun h => ⟨h.op, h.inputs.map remap⟩)
    let out' : ℕ := remap out
    have hlen' : gs'.length + 1 = gs.length := by
      simp only [gs', List.length_append, List.length_take, List.length_map, List.length_drop]
      omega
    have hget_lt : ∀ j < k, gs'[j]? = gs[j]? := by
      intro j hj
      have ht : (gs.take k).length = k := by rw [List.length_take]; omega
      simp only [gs', List.getElem?_append_left (by omega : j < (gs.take k).length),
        List.getElem?_take_of_lt hj]
    have hget_ge : ∀ j, k ≤ j → j < gs'.length →
        gs'[j]? = (gs[j + 1]?).map (fun h => ⟨h.op, h.inputs.map remap⟩) := by
      intro j hkj hj
      have ht : (gs.take k).length = k := by rw [List.length_take]; omega
      simp only [gs', List.getElem?_append_right (by omega : (gs.take k).length ≤ j), ht,
        List.getElem?_map, List.getElem?_drop]
      have hidx : k + 1 + (j - k) = j + 1 := by omega
      rw [hidx]
    have hval' : Valid gs' := by
      refine ⟨?_, ?_⟩
      · intro g hg
        simp only [gs', List.mem_append, List.mem_map] at hg
        rcases hg with h1 | ⟨h, hh, rfl⟩
        · exact hval.1 g (List.mem_of_mem_take h1)
        · have hh' := hval.1 h (List.mem_of_mem_drop hh)
          exact ⟨hh'.1, by simpa using hh'.2⟩
      · intro j g hgj w hw
        have hj : j < gs'.length := (List.getElem?_eq_some_iff.mp hgj).1
        by_cases hjk : j < k
        · rw [hget_lt j hjk] at hgj
          exact hval.2 j g hgj w hw
        · rw [hget_ge j (by omega) hj] at hgj
          have hj1 : j + 1 < gs.length := by omega
          rw [List.getElem?_eq_getElem hj1, Option.map_some] at hgj
          have hgeq := Option.some.inj hgj
          rw [← hgeq] at hw
          simp only [List.mem_map] at hw
          obtain ⟨u, hu, rfl⟩ := hw
          have hu_lt := hval.2 (j + 1) gs[j + 1] (List.getElem?_eq_getElem hj1) u hu
          dsimp only [remap]
          split_ifs <;> omega
    have hwires_eq : ∀ (x : List Bool), x.length = 26 → ∀ m < 26 + gs'.length,
        (Circuit.wires ⟨gs', 0⟩ x).getD m false =
          (Circuit.wires ⟨gs, 0⟩ x).getD (if m < 26 + k then m else m + 1) false := by
      intro x hx m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro hm
        by_cases hm26 : m < 26
        · have hm26' : m < 26 + k := by omega
          rw [if_pos hm26', hwire_in gs' x m (by omega), hwire_in gs x m (by omega)]
        · let j := m - 26
          have hj_eq : 26 + j = m := by omega
          have hj_lt : j < gs'.length := by omega
          rw [← hj_eq]
          by_cases hjk : j < k
          · have hlt : 26 + j < 26 + k := by omega
            rw [if_pos hlt]
            have hgj : gs'[j]? = some gs'[j] := List.getElem?_eq_getElem hj_lt
            have hgj_old : gs[j]? = some gs'[j] := by rwa [← hget_lt j hjk]
            rw [hwire_gate gs' x j gs'[j] hx hgj (hval'.2 j gs'[j] hgj),
              hwire_gate gs x j gs'[j] hx hgj_old (hval.2 j gs'[j] hgj_old)]
            congr 1
            apply List.map_congr_left
            intro w hw
            have hw_lt := hval'.2 j gs'[j] hgj w hw
            have ihw := ih w (by omega) (by omega)
            rwa [if_pos (by omega)] at ihw
          · have hge : ¬ (26 + j < 26 + k) := by omega
            rw [if_neg hge]
            have hj1_lt : j + 1 < gs.length := by omega
            have hfold : 26 + j + 1 = 26 + (j + 1) := by omega
            rw [hfold]
            have hg_new : gs'[j]? = some ⟨gs[j + 1].op, gs[j + 1].inputs.map remap⟩ := by
              rw [hget_ge j (by omega) hj_lt, List.getElem?_eq_getElem hj1_lt, Option.map_some]
            have hg_old : gs[j + 1]? = some gs[j + 1] := List.getElem?_eq_getElem hj1_lt
            rw [hwire_gate gs' x j _ hx hg_new (hval'.2 j _ hg_new),
              hwire_gate gs x (j + 1) _ hx hg_old (hval.2 (j + 1) _ hg_old)]
            dsimp only
            rw [List.map_map]
            congr 1
            apply List.map_congr_left
            intro w hw
            have hw_lt := hval.2 (j + 1) _ hg_old w hw
            have hrm_lt : remap w < 26 + j := by
              dsimp only [remap]; split_ifs <;> omega
            have ihw := ih (remap w) (by omega) (by omega)
            dsimp only [Function.comp_apply]
            rw [ihw]
            by_cases hwk : w = 26 + k
            · have harg : (if remap w < 26 + k then remap w else remap w + 1) = a := by
                dsimp only [remap]; split_ifs <;> omega
              rw [harg, hwk, halias x hx]
            · have harg : (if remap w < 26 + k then remap w else remap w + 1) = w := by
                dsimp only [remap]; split_ifs <;> omega
              rw [harg]
    refine ⟨gs', out', hlen', hval', ?_⟩
    intro x hx
    change (Circuit.wires ⟨gs', 0⟩ x).getD out' false = (Circuit.wires ⟨gs, 0⟩ x).getD out false
    have hout'_lt : out' < 26 + gs'.length := by
      dsimp only [out', remap]; split_ifs <;> omega
    rw [hwires_eq x hx out' hout'_lt]
    by_cases hok : out = 26 + k
    · have harg : (if out' < 26 + k then out' else out' + 1) = a := by
        dsimp only [out', remap]; split_ifs <;> omega
      rw [harg, hok, halias x hx]
    · have harg : (if out' < 26 + k then out' else out' + 1) = out := by
        dsimp only [out', remap]; split_ifs <;> omega
      rw [harg]
  have helim_const : ∀ (gs : List Gate) (out k : ℕ) (c : Bool), Valid gs →
      k < gs.length → out < 26 + gs.length → out ≠ 26 + k →
      (∀ x : List Bool, x.length = 26 → (Circuit.wires ⟨gs, 0⟩ x).getD (26 + k) false = c) →
      ∃ (gs' : List Gate) (out' : ℕ), gs'.length + 1 = gs.length ∧ Valid gs' ∧
        ∀ x : List Bool, x.length = 26 →
          Circuit.eval ⟨gs', out'⟩ x = Circuit.eval ⟨gs, out⟩ x := by
    intro gs out k c hval hk hout hne hconst
    let shift (w : ℕ) : ℕ := if 26 + k < w then w - 1 else w
    let xform (h : Gate) : Gate :=
      if 26 + k ∈ h.inputs then
        match h.op with
        | GateOp.and => if c then ⟨GateOp.and, (h.inputs.filter (fun w => decide (w ≠ 26 + k))).map shift⟩ else ⟨GateOp.or, []⟩
        | GateOp.or => if c then ⟨GateOp.and, []⟩ else ⟨GateOp.or, (h.inputs.filter (fun w => decide (w ≠ 26 + k))).map shift⟩
        | GateOp.not => ⟨h.op, h.inputs.map shift⟩
        | GateOp.mod _ => ⟨h.op, h.inputs.map shift⟩
        | GateOp.maj => ⟨h.op, h.inputs.map shift⟩
      else
        ⟨h.op, h.inputs.map shift⟩
    let gs' : List Gate := gs.take k ++ (gs.drop (k + 1)).map xform
    let out' : ℕ := shift out
    have hlen' : gs'.length + 1 = gs.length := by
      simp only [gs', List.length_append, List.length_take, List.length_map, List.length_drop]
      omega
    have hget_lt : ∀ j < k, gs'[j]? = gs[j]? := by
      intro j hj
      have ht : (gs.take k).length = k := by rw [List.length_take]; omega
      simp only [gs', List.getElem?_append_left (by omega : j < (gs.take k).length),
        List.getElem?_take_of_lt hj]
    have hget_ge : ∀ j, k ≤ j → j < gs'.length → gs'[j]? = (gs[j + 1]?).map xform := by
      intro j hkj hj
      have ht : (gs.take k).length = k := by rw [List.length_take]; omega
      simp only [gs', List.getElem?_append_right (by omega : (gs.take k).length ≤ j), ht,
        List.getElem?_map, List.getElem?_drop]
      have hidx : k + 1 + (j - k) = j + 1 := by omega
      rw [hidx]
    have hval' : Valid gs' := by
      refine ⟨?_, ?_⟩
      · intro g hg
        simp only [gs', List.mem_append, List.mem_map] at hg
        rcases hg with h1 | ⟨h, hh, rfl⟩
        · exact hval.1 g (List.mem_of_mem_take h1)
        · obtain ⟨hop, hlen⟩ := hval.1 h (List.mem_of_mem_drop hh)
          dsimp only [xform]
          by_cases hmem : 26 + k ∈ h.inputs
          · rw [if_pos hmem]
            rcases hop with hop | hop <;> rw [hop] <;> dsimp only <;> by_cases hc : c = true
            · rw [if_pos hc]; exact ⟨Or.inl rfl, by simpa using (List.length_filter_le _ _).trans hlen⟩
            · rw [if_neg hc]; exact ⟨Or.inr rfl, by simp⟩
            · rw [if_pos hc]; exact ⟨Or.inl rfl, by simp⟩
            · rw [if_neg hc]; exact ⟨Or.inr rfl, by simpa using (List.length_filter_le _ _).trans hlen⟩
          · rw [if_neg hmem]; exact ⟨hop, by simpa using hlen⟩
      · intro j g hgj w hw
        have hj : j < gs'.length := (List.getElem?_eq_some_iff.mp hgj).1
        by_cases hjk : j < k
        · rw [hget_lt j hjk] at hgj
          exact hval.2 j g hgj w hw
        · rw [hget_ge j (by omega) hj] at hgj
          have hj1 : j + 1 < gs.length := by omega
          rw [List.getElem?_eq_getElem hj1, Option.map_some] at hgj
          have hgeq := Option.some.inj hgj
          rw [← hgeq] at hw
          have hrb := hval.2 (j + 1) gs[j + 1] (List.getElem?_eq_getElem hj1)
          have hop := (hval.1 gs[j + 1] (List.getElem_mem hj1)).1
          dsimp only [xform] at hw
          by_cases hmem : 26 + k ∈ gs[j + 1].inputs
          · rw [if_pos hmem] at hw
            rcases hop with hop | hop <;> rw [hop] at hw <;> dsimp only at hw <;> by_cases hc : c = true
            · rw [if_pos hc] at hw
              simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
              obtain ⟨u, ⟨hu, hune⟩, rfl⟩ := hw
              have := hrb u hu
              dsimp only [shift]; split_ifs <;> omega
            · rw [if_neg hc] at hw; simp at hw
            · rw [if_pos hc] at hw; simp at hw
            · rw [if_neg hc] at hw
              simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
              obtain ⟨u, ⟨hu, hune⟩, rfl⟩ := hw
              have := hrb u hu
              dsimp only [shift]; split_ifs <;> omega
          · rw [if_neg hmem] at hw
            simp only [List.mem_map] at hw
            obtain ⟨u, hu, rfl⟩ := hw
            have hune : u ≠ 26 + k := fun heq => hmem (heq ▸ hu)
            have := hrb u hu
            dsimp only [shift]; split_ifs <;> omega
    have hall_filter : ∀ (f : ℕ → Bool) (l : List ℕ), f (26 + k) = true →
        ((l.filter (fun w => decide (w ≠ 26 + k))).map f).all id = (l.map f).all id := by
      intro f l hf
      induction l with
      | nil => rfl
      | cons u l ih =>
        by_cases hu : u = 26 + k
        · subst hu
          simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ↓reduceIte, List.map_cons, List.all_cons, id_eq, hf, Bool.true_and]
          exact ih
        · simp only [List.filter_cons, ne_eq, hu, not_false_eq_true, decide_true, ↓reduceIte,
            List.map_cons, List.all_cons, id_eq, ih]
    have hany_filter : ∀ (f : ℕ → Bool) (l : List ℕ), f (26 + k) = false →
        ((l.filter (fun w => decide (w ≠ 26 + k))).map f).any id = (l.map f).any id := by
      intro f l hf
      induction l with
      | nil => rfl
      | cons u l ih =>
        by_cases hu : u = 26 + k
        · subst hu
          simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
            ↓reduceIte, List.map_cons, List.any_cons, id_eq, hf, Bool.false_or]
          exact ih
        · simp only [List.filter_cons, ne_eq, hu, not_false_eq_true, decide_true, ↓reduceIte,
            List.map_cons, List.any_cons, id_eq, ih]
    have hall_false : ∀ (f : ℕ → Bool) (l : List ℕ), 26 + k ∈ l → f (26 + k) = false →
        (l.map f).all id = false := by
      intro f l hmem hf
      induction l with
      | nil => simp at hmem
      | cons u l ih =>
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · simp [hf]
        · simp [ih hmem]
    have hany_true : ∀ (f : ℕ → Bool) (l : List ℕ), 26 + k ∈ l → f (26 + k) = true →
        (l.map f).any id = true := by
      intro f l hmem hf
      induction l with
      | nil => simp at hmem
      | cons u l ih =>
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · simp [hf]
        · simp [ih hmem]
    have hwires_eq : ∀ (x : List Bool), x.length = 26 → ∀ m < 26 + gs'.length,
        (Circuit.wires ⟨gs', 0⟩ x).getD m false =
          (Circuit.wires ⟨gs, 0⟩ x).getD (if m < 26 + k then m else m + 1) false := by
      intro x hx m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro hm
        by_cases hm26 : m < 26
        · have hm26' : m < 26 + k := by omega
          rw [if_pos hm26', hwire_in gs' x m (by omega), hwire_in gs x m (by omega)]
        · let j := m - 26
          have hj_eq : 26 + j = m := by omega
          have hj_lt : j < gs'.length := by omega
          rw [← hj_eq]
          by_cases hjk : j < k
          · have hlt : 26 + j < 26 + k := by omega
            rw [if_pos hlt]
            have hgj : gs'[j]? = some gs'[j] := List.getElem?_eq_getElem hj_lt
            have hgj_old : gs[j]? = some gs'[j] := by rwa [← hget_lt j hjk]
            rw [hwire_gate gs' x j gs'[j] hx hgj (hval'.2 j gs'[j] hgj),
              hwire_gate gs x j gs'[j] hx hgj_old (hval.2 j gs'[j] hgj_old)]
            congr 1
            apply List.map_congr_left
            intro w hw
            have hw_lt := hval'.2 j gs'[j] hgj w hw
            have ihw := ih w (by omega) (by omega)
            rwa [if_pos (by omega)] at ihw
          · have hge : ¬ (26 + j < 26 + k) := by omega
            rw [if_neg hge]
            have hj1_lt : j + 1 < gs.length := by omega
            have hfold : 26 + j + 1 = 26 + (j + 1) := by omega
            rw [hfold]
            have hg_new : gs'[j]? = some (xform gs[j + 1]) := by
              rw [hget_ge j (by omega) hj_lt, List.getElem?_eq_getElem hj1_lt, Option.map_some]
            have hg_old : gs[j + 1]? = some gs[j + 1] := List.getElem?_eq_getElem hj1_lt
            rw [hwire_gate gs' x j _ hx hg_new (hval'.2 j _ hg_new),
              hwire_gate gs x (j + 1) _ hx hg_old (hval.2 (j + 1) _ hg_old)]
            have hrb := hval.2 (j + 1) gs[j + 1] hg_old
            have hop := (hval.1 gs[j + 1] (List.getElem_mem hj1_lt)).1
            have hshift_eq : ∀ u ∈ gs[j + 1].inputs, u ≠ 26 + k →
                (Circuit.wires ⟨gs', 0⟩ x).getD (shift u) false =
                  (Circuit.wires ⟨gs, 0⟩ x).getD u false := by
              intro u hu hune
              have hu_lt := hrb u hu
              have hsu_lt : shift u < 26 + j := by dsimp only [shift]; split_ifs <;> omega
              have ihu := ih (shift u) (by omega) (by omega)
              rw [ihu]
              have harg : (if shift u < 26 + k then shift u else shift u + 1) = u := by
                dsimp only [shift]; split_ifs <;> omega
              rw [harg]
            dsimp only [xform]
            by_cases hmem : 26 + k ∈ gs[j + 1].inputs
            · rw [if_pos hmem]
              rcases hop with hop | hop <;> rw [hop] <;> dsimp only <;> by_cases hc : c = true
              · rw [if_pos hc]
                rw [evalAnd, evalAnd]
                simp only [List.map_map]
                have hmap : (gs[j + 1].inputs.filter (fun w => decide (w ≠ 26 + k))).map
                    ((fun w => (Circuit.wires ⟨gs', 0⟩ x).getD w false) ∘ shift) =
                    (gs[j + 1].inputs.filter (fun w => decide (w ≠ 26 + k))).map
                    (fun w => (Circuit.wires ⟨gs, 0⟩ x).getD w false) := by
                  apply List.map_congr_left
                  intro u hu
                  have ⟨hu1, hu2⟩ := List.mem_filter.mp hu
                  exact hshift_eq u hu1 (of_decide_eq_true hu2)
                rw [hmap]
                exact hall_filter _ _ (by rw [hconst x hx, hc])
              · rw [if_neg hc]
                have hcf : c = false := Bool.eq_false_iff.mpr hc
                rw [evalOr, evalAnd]
                simp only [List.map_nil, List.any_nil]
                exact (hall_false _ _ hmem (by rw [hconst x hx, hcf])).symm
              · rw [if_pos hc]
                rw [evalAnd, evalOr]
                simp only [List.map_nil, List.all_nil]
                exact (hany_true _ _ hmem (by rw [hconst x hx, hc])).symm
              · rw [if_neg hc]
                have hcf : c = false := Bool.eq_false_iff.mpr hc
                rw [evalOr, evalOr]
                simp only [List.map_map]
                have hmap : (gs[j + 1].inputs.filter (fun w => decide (w ≠ 26 + k))).map
                    ((fun w => (Circuit.wires ⟨gs', 0⟩ x).getD w false) ∘ shift) =
                    (gs[j + 1].inputs.filter (fun w => decide (w ≠ 26 + k))).map
                    (fun w => (Circuit.wires ⟨gs, 0⟩ x).getD w false) := by
                  apply List.map_congr_left
                  intro u hu
                  have ⟨hu1, hu2⟩ := List.mem_filter.mp hu
                  exact hshift_eq u hu1 (of_decide_eq_true hu2)
                rw [hmap]
                exact hany_filter _ _ (by rw [hconst x hx, hcf])
            · rw [if_neg hmem]
              dsimp only
              rw [List.map_map]
              congr 1
              apply List.map_congr_left
              intro u hu
              exact hshift_eq u hu (fun heq => hmem (heq ▸ hu))
    refine ⟨gs', out', hlen', hval', ?_⟩
    intro x hx
    change (Circuit.wires ⟨gs', 0⟩ x).getD out' false = (Circuit.wires ⟨gs, 0⟩ x).getD out false
    have hout'_lt : out' < 26 + gs'.length := by
      dsimp only [out', shift]; split_ifs <;> omega
    rw [hwires_eq x hx out' hout'_lt]
    have harg : (if out' < 26 + k then out' else out' + 1) = out := by
      dsimp only [out', shift]; split_ifs <;> omega
    rw [harg]
  have hnorm : ∀ (n : ℕ) (gs : List Gate) (out : ℕ), gs.length = n → Valid gs →
      (∃ x : List Bool, x.length = 26 ∧ Circuit.eval ⟨gs, out⟩ x = true) →
      (∃ y : List Bool, y.length = 26 ∧ Circuit.eval ⟨gs, out⟩ y = false) →
      ∃ C' : Circuit, C'.size ≤ gs.length ∧ Strict C'.gates ∧
        ∀ x : List Bool, x.length = 26 → C'.eval x = Circuit.eval ⟨gs, out⟩ x := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro gs out hlen hval ⟨x0, hx0_len, hx0⟩ ⟨y0, hy0_len, hy0⟩
      have hout_lt : out < 26 + gs.length := by
        by_contra hge
        push Not at hge
        have hfalse : Circuit.eval ⟨gs, out⟩ x0 = false :=
          hwire_big gs x0 out (by omega)
        rw [hfalse] at hx0
        exact Bool.false_ne_true hx0
      by_cases hstr : Strict gs
      · exact ⟨⟨gs, out⟩, le_rfl, hstr, fun _ _ => rfl⟩
      · simp only [Strict, not_forall] at hstr
        obtain ⟨k, g, hgk, hbad⟩ := hstr
        have hk : k < gs.length := (List.getElem?_eq_some_iff.mp hgk).1
        obtain ⟨hop, hilen⟩ := hval.1 g (List.mem_of_getElem? hgk)
        have hrb := hval.2 k g hgk
        rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
        · have hconst : ∀ x : List Bool, x.length = 26 →
              (Circuit.wires ⟨gs, 0⟩ x).getD (26 + k) false = g.op.eval [] := by
            intro x hx
            rw [hwire_gate gs x k g hx hgk hrb, hin]; rfl
          have hne : out ≠ 26 + k := by
            intro heq
            have h1 : Circuit.eval ⟨gs, out⟩ x0 = g.op.eval [] := by
              change (Circuit.wires ⟨gs, 0⟩ x0).getD out false = _; rw [heq]; exact hconst x0 hx0_len
            have h2 : Circuit.eval ⟨gs, out⟩ y0 = g.op.eval [] := by
              change (Circuit.wires ⟨gs, 0⟩ y0).getD out false = _; rw [heq]; exact hconst y0 hy0_len
            rw [h1] at hx0; rw [h2] at hy0
            rw [hx0] at hy0; exact Bool.false_ne_true hy0.symm
          obtain ⟨gs', out', hlen', hval', hev'⟩ :=
            helim_const gs out k (g.op.eval []) hval hk hout_lt hne hconst
          obtain ⟨C', hsz', hstr', hcev'⟩ :=
            ih gs'.length (by omega) gs' out' rfl hval'
              ⟨x0, hx0_len, by rw [hev' x0 hx0_len]; exact hx0⟩
              ⟨y0, hy0_len, by rw [hev' y0 hy0_len]; exact hy0⟩
          exact ⟨C', by change C'.gates.length ≤ gs.length; change C'.gates.length ≤ gs'.length at hsz'; omega,
            hstr', fun x hx => by rw [hcev' x hx, hev' x hx]⟩
        · have ha : a < 26 + k := hrb a (by simp [hin])
          have halias : ∀ x : List Bool, x.length = 26 →
              (Circuit.wires ⟨gs, 0⟩ x).getD (26 + k) false = (Circuit.wires ⟨gs, 0⟩ x).getD a false := by
            intro x hx
            rw [hwire_gate gs x k g hx hgk hrb, hin]
            rcases hop with hop | hop
            · rw [hop, evalAnd]; simp
            · rw [hop, evalOr]; simp
          obtain ⟨gs', out', hlen', hval', hev'⟩ :=
            helim_alias gs out k a hval hk hout_lt ha halias
          obtain ⟨C', hsz', hstr', hcev'⟩ :=
            ih gs'.length (by omega) gs' out' rfl hval'
              ⟨x0, hx0_len, by rw [hev' x0 hx0_len]; exact hx0⟩
              ⟨y0, hy0_len, by rw [hev' y0 hy0_len]; exact hy0⟩
          exact ⟨C', by change C'.gates.length ≤ gs.length; change C'.gates.length ≤ gs'.length at hsz'; omega,
            hstr', fun x hx => by rw [hcev' x hx, hev' x hx]⟩
        · have ha : a < 26 + k := hrb a (by simp [hin])
          have hb : b < 26 + k := hrb b (by simp [hin])
          have hab : a = b := by
            by_contra hne
            exact hbad ⟨hop, a, b, hin, hne, ha, hb⟩
          subst hab
          have halias : ∀ x : List Bool, x.length = 26 →
              (Circuit.wires ⟨gs, 0⟩ x).getD (26 + k) false = (Circuit.wires ⟨gs, 0⟩ x).getD a false := by
            intro x hx
            rw [hwire_gate gs x k g hx hgk hrb, hin]
            rcases hop with hop | hop
            · rw [hop, evalAnd]; simp
            · rw [hop, evalOr]; simp
          obtain ⟨gs', out', hlen', hval', hev'⟩ :=
            helim_alias gs out k a hval hk hout_lt ha halias
          obtain ⟨C', hsz', hstr', hcev'⟩ :=
            ih gs'.length (by omega) gs' out' rfl hval'
              ⟨x0, hx0_len, by rw [hev' x0 hx0_len]; exact hx0⟩
              ⟨y0, hy0_len, by rw [hev' y0 hy0_len]; exact hy0⟩
          exact ⟨C', by change C'.gates.length ≤ gs.length; change C'.gates.length ≤ gs'.length at hsz'; omega,
            hstr', fun x hx => by rw [hcev' x hx, hev' x hx]⟩
        · rw [hin] at hilen; simp at hilen
  have hval0 : Valid gates := by
    refine ⟨hops, ?_⟩
    intro j g hgj w hw
    have hj : j < gates.length := (List.getElem?_eq_some_iff.mp hgj).1
    have hgeq : gates.get ⟨j, hj⟩ = g := by
      simpa [List.getElem?_eq_getElem hj] using hgj
    rw [← hgeq] at hw
    exact hreads ⟨j, hj⟩ w hw
  have hmem_singer : ∀ p l : Fin 13,
      p ∈ singerLines3 l ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
  have hx0 : ∃ x : List Bool, x.length = 26 ∧ Circuit.eval ⟨gates, out⟩ x = true := by
    refine ⟨List.ofFn (fun u1 : Fin 13 => decide (u1 = 0)) ++
      List.ofFn (fun v1 : Fin 13 => decide (v1 = 0)), by simp, hpos 0 0 (by decide)⟩
  have hy0 : ∃ y : List Bool, y.length = 26 ∧ Circuit.eval ⟨gates, out⟩ y = false := by
    let Q0 : Finset (Fin 13) := {0, 1, 2, 5}
    have hQ0_card : Q0.card = 4 := by decide
    have hQ0_col : ∀ k : Fin 13,
        (Q0.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2 := by decide
    refine ⟨List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q0)) ++
      List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q0, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))),
      by simp, hneg Q0 hQ0_card hQ0_col⟩
  obtain ⟨C', hsz', hstr', hcev'⟩ := hnorm gates.length gates out rfl hval0 hx0 hy0
  have hpos' : ∀ p l : Fin 13, p ∈ singerLines3 l →
      C'.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))) = true := by
    intro p l hpl
    rw [hcev' _ (by simp)]
    exact hpos p l ((hmem_singer p l).mp hpl)
  have hneg' : ∀ Q ∈ quadrangles singerLines3,
      C'.eval (List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q))) = false := by
    intro Q hQ
    rw [hquadDef] at hQ
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and] at hQ
    have hcol : ∀ k : Fin 13,
        (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2 := by
      intro k
      have heq : Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13))) =
          Q ∩ singerLines3 k := by
        ext u; simp [hmem_singer]
      rw [heq]
      exact hQ.2 k
    have hmiss : (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) =
        (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) := by
      funext v
      apply decide_eq_decide.mpr
      rw [hmissDef]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right]
      constructor
      · intro h r hr hrv
        exact h hr ((hmem_singer r v).mpr hrv)
      · intro h r hr hrv
        exact h r hr ((hmem_singer r v).mp hrv)
    rw [hmiss, hcev' _ (by simp)]
    exact hneg Q hQ.1 hcol
  let E : List (ℕ × ℕ) := (List.finRange 13).flatMap fun p =>
    ((List.finRange 13).filter fun l => decide (p ∈ singerLines3 l)).map fun l => (p.val, 13 + l.val)
  have hge64 : 64 ≤ C'.size := by
    by_cases hsr : IsSingleRead C' 26 (fun i => decide (13 ≤ i)) E
    · exact hSingle C' hstr' hpos' hneg' hsr
    · exact hDouble C' hstr' hpos' hneg' hsr
  exact hge64.trans hsz'
