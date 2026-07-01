def StrictlyIncreasingOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  forall (x y : Power R 1) (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f ⟨x, hx⟩).1 (f ⟨y, hy⟩).1

def StrictlyDecreasingOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  forall (x y : Power R 1) (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f ⟨y, hy⟩).1 (f ⟨x, hx⟩).1

def StrictlyMonotoneOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  StrictlyIncreasingOn D I B f \/ StrictlyDecreasingOn D I B f

lemma exists_finite_between_of_extended_interval
    (h : Endpoint.lt D a (Endpoint.finite x) /\ Endpoint.lt D (Endpoint.finite x) b) :
    exists c d : R,
      Endpoint.lt D a (Endpoint.finite c) /\ D.lt c x /\
      D.lt x d /\ Endpoint.lt D (Endpoint.finite d) b := by
  cases a <;> cases b <;> try exact h.1.elim
  · exact (h.2).elim
  · rcases D.no_left_endpoint x with ⟨c, hcx⟩
    rcases D.dense h.2 with ⟨d, hxd, hdb⟩
    exact ⟨c, d, trivial, hcx, hxd, hdb⟩
  · rcases D.no_left_endpoint x with ⟨c, hcx⟩
    rcases D.no_right_endpoint x with ⟨d, hxd⟩
    exact ⟨c, d, trivial, hcx, hxd, trivial⟩
  · exact (h.2).elim
  · rcases D.dense h.1 with ⟨c, hac, hcx⟩
    rcases D.dense h.2 with ⟨d, hxd, hdb⟩
    exact ⟨c, d, hac, hcx, hxd, hdb⟩
  · rcases D.dense h.1 with ⟨c, hac, hcx⟩
    rcases D.no_right_endpoint x with ⟨d, hxd⟩
    exact ⟨c, d, hac, hcx, hxd, trivial⟩

lemma lt_of_lt_of_lt_finite {x : Endpoint R} {c y : R}
    (h1 : Endpoint.lt D x (Endpoint.finite c)) (h2 : D.lt c y) :
    Endpoint.lt D x (Endpoint.finite y) := by
  cases x with
  | negInf => exact trivial
  | finite a => exact D.trans h1 h2
  | posInf => exfalso; exact h1

lemma lt_of_finite_lt_of_lt {x : Endpoint R} {y d : R}
    (h1 : D.lt y d) (h2 : Endpoint.lt D (Endpoint.finite d) x) :
    Endpoint.lt D (Endpoint.finite y) x := by
  cases x with
  | negInf => exfalso; exact h2
  | finite b => exact D.trans h1 h2
  | posInf => exact trivial

lemma preimage_of_open_interval
    (f : DefinableFunction M I B) (hmono : StrictlyMonotoneOn D I B f.toFun)
    (hDomain : (openInterval D a b).Subset I)
    (hSurj : forall y, openInterval D (Endpoint.finite r) (Endpoint.finite s) y ->
    exists x, openInterval D a b x /\ exists hx, (f.toFun ⟨x, hx⟩).1 = y)
    {l h : R} (hlh : D.lt l h) (h_lr : D.lt r l) (h_hs : D.lt h s) :
    exists al be : Endpoint R,
      Endpoint.lt D al be /\
      (forall x : Power R 1,
         openInterval D al be x <->
           openInterval D a b x /\
           exists hx : I x,
             openInterval D (Endpoint.finite l) (Endpoint.finite h) (f.toFun ⟨x, hx⟩).1) := by
  have h_ls : D.lt l s := D.trans hlh h_hs
  have h_rh : D.lt r h := D.trans h_lr hlh
  rcases hmono with hinc | hdec
  · have hl_in : openInterval D (Endpoint.finite r) (Endpoint.finite s) (fun _ => l) := by
      exact ⟨by simpa [Power.coord1] using h_lr, by simpa [Power.coord1] using h_ls⟩
    have hh_in : openInterval D (Endpoint.finite r) (Endpoint.finite s) (fun _ => h) := by
      exact ⟨by simpa [Power.coord1] using h_rh, by simpa [Power.coord1] using h_hs⟩
    rcases hSurj (fun _ => l) hl_in with ⟨u, hu_ab, huI, hu_eq⟩
    rcases hSurj (fun _ => h) hh_in with ⟨v, hv_ab, hvI, hv_eq⟩
    have huv : D.lt (Power.coord1 u) (Power.coord1 v) := by
      rcases D.trichotomy (Power.coord1 u) (Power.coord1 v) with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
      · exact hlt
      · exfalso
        have hu_eqv : u = v := by
          ext i; fin_cases i; exact heq
        have hll : D.lt l l := by
          have hcoord : l = h := by
            have hEq : f.toFun ⟨u, huI⟩ = f.toFun ⟨v, hvI⟩ := by congr
            simpa [hu_eq, hv_eq, Power.coord1] using congrArg (fun z => Power.coord1 z) (congrArg (fun z => z.1) hEq)
          simpa [hcoord] using hlh
        exact D.irrefl l hll
      · exfalso
        have hhl : D.lt h l := by
          simpa [hu_eq, hv_eq] using hinc v u hvI huI hgt
        exact False.elim (D.irrefl l (D.trans hlh hhl))
    refine ⟨Endpoint.finite (Power.coord1 u), Endpoint.finite (Power.coord1 v), huv, ?_⟩
    intro x
    constructor
    · intro hx
      rcases hx with ⟨hux, hxv⟩
      rcases hu_ab with ⟨hau, hub⟩
      rcases hv_ab with ⟨hav, hvb⟩
      have hx_ab : openInterval D a b x := by
        constructor
        · exact lt_of_lt_of_lt_finite hau (by simpa using hux)
        · exact lt_of_finite_lt_of_lt (by simpa using hxv) hvb
      have hxI : I x := hDomain hx_ab
      refine ⟨hx_ab, hxI, ?_⟩
      constructor
      · have hlu : D.lt l (Power.coord1 (f.toFun ⟨x, hxI⟩).1) := by
          have hux' : D.lt (Power.coord1 u) (Power.coord1 x) := by simpa using hux
          have hfux : D.lt (Power.coord1 (f.toFun ⟨u, huI⟩).1) (Power.coord1 (f.toFun ⟨x, hxI⟩).1) :=
            hinc u x huI hxI hux'
          simpa [hu_eq, Power.coord1] using hfux
        exact hlu
      · have hxh : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) h := by
          have hxv' : D.lt (Power.coord1 x) (Power.coord1 v) := by simpa using hxv
          have hfxv : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) (Power.coord1 (f.toFun ⟨v, hvI⟩).1) :=
            hinc x v hxI hvI hxv'
          simpa [hv_eq, Power.coord1] using hfxv
        exact hxh
    · intro hx
      rcases hx with ⟨hx_ab, hxI, hfx⟩
      rcases hu_ab with ⟨hau, hub⟩
      rcases hv_ab with ⟨hav, hvb⟩
      have h_lfx : D.lt l (Power.coord1 (f.toFun ⟨x, hxI⟩).1) := by
        simpa [Power.coord1] using hfx.1
      have h_fxh : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) h := by
        simpa [Power.coord1] using hfx.2
      have hux : D.lt (Power.coord1 u) (Power.coord1 x) := by
        rcases D.trichotomy (Power.coord1 u) (Power.coord1 x) with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
        · exact hlt
        · exfalso
          have hu_eqx : u = x := by ext i; fin_cases i; exact heq
          have hll : D.lt l l := by
            have hlu_u : D.lt l (Power.coord1 (f.toFun ⟨u, huI⟩).1) := by
              have hEq : f.toFun ⟨u, huI⟩ = f.toFun ⟨x, hxI⟩ := by congr
              simpa [hEq, Power.coord1] using h_lfx
            simpa [hu_eq, Power.coord1] using hlu_u
          exact D.irrefl l hll
        · exfalso
          have hfxl : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) l := by
            simpa [hu_eq, Power.coord1] using hinc x u hxI huI hgt
          exact D.irrefl l (D.trans h_lfx hfxl)
      have hxv : D.lt (Power.coord1 x) (Power.coord1 v) := by
        rcases D.trichotomy (Power.coord1 x) (Power.coord1 v) with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
        · exact hlt
        · exfalso
          have hx_eqv : x = v := by ext i; fin_cases i; exact heq
          have hhh : D.lt h h := by
            have hEq : f.toFun ⟨x, hxI⟩ = f.toFun ⟨v, hvI⟩ := by congr
            simpa [hv_eq, Power.coord1, hEq] using h_fxh
          exact D.irrefl h hhh
        · exfalso
          have hfxh : D.lt h (Power.coord1 (f.toFun ⟨x, hxI⟩).1) := by
            simpa [hv_eq, Power.coord1] using hinc v x hvI hxI hgt
          exact D.irrefl h (D.trans hfxh h_fxh)
      constructor
      · exact by simpa [Endpoint.finite] using hux
      · exact by simpa [Endpoint.finite] using hxv
  · have hl_in : openInterval D (Endpoint.finite r) (Endpoint.finite s) (fun _ => l) := by
      exact ⟨by simpa [Power.coord1] using h_lr, by simpa [Power.coord1] using h_ls⟩
    have hh_in : openInterval D (Endpoint.finite r) (Endpoint.finite s) (fun _ => h) := by
      exact ⟨by simpa [Power.coord1] using h_rh, by simpa [Power.coord1] using h_hs⟩
    rcases hSurj (fun _ => l) hl_in with ⟨u, hu_ab, huI, hu_eq⟩
    rcases hSurj (fun _ => h) hh_in with ⟨v, hv_ab, hvI, hv_eq⟩
    have huv : D.lt (Power.coord1 v) (Power.coord1 u) := by
      rcases D.trichotomy (Power.coord1 v) (Power.coord1 u) with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
      · exact hlt
      · exfalso
        have hv_equ : v = u := by ext i; fin_cases i; exact heq
        have hll : D.lt h h := by
          have h_eq_h_l : h = l := by
            have hEq_val : (f.toFun ⟨v, hvI⟩).1 = (f.toFun ⟨u, huI⟩).1 := by
              simpa using congrArg (fun z => (f.toFun z).1) (by
                apply Subtype.ext; exact hv_equ)
            simpa [hv_eq, hu_eq, Power.coord1] using congrArg (fun z => Power.coord1 z) hEq_val
          simpa [h_eq_h_l] using hlh
        exact D.irrefl h hll
      · exfalso
        have hhl : D.lt h l := by
          simpa [hv_eq, hu_eq] using hdec u v huI hvI hgt
        exact False.elim (D.irrefl l (D.trans hlh hhl))
    refine ⟨Endpoint.finite (Power.coord1 v), Endpoint.finite (Power.coord1 u), huv, ?_⟩
    intro x
    constructor
    · intro hx
      rcases hx with ⟨hvx, hxu⟩
      rcases hu_ab with ⟨hau, hub⟩
      rcases hv_ab with ⟨hav, hvb⟩
      have hx_ab : openInterval D a b x := by
        constructor
        · exact lt_of_lt_of_lt_finite hav (by simpa using hvx)
        · exact lt_of_finite_lt_of_lt (by simpa using hxu) hub
      have hxI : I x := hDomain hx_ab
      refine ⟨hx_ab, hxI, ?_⟩
      constructor
      · have hlu : D.lt l (Power.coord1 (f.toFun ⟨x, hxI⟩).1) := by
          have hxu' : D.lt (Power.coord1 x) (Power.coord1 u) := by simpa using hxu
          have hfux : D.lt (Power.coord1 (f.toFun ⟨u, huI⟩).1) (Power.coord1 (f.toFun ⟨x, hxI⟩).1) :=
            hdec x u hxI huI hxu'
          simpa [hu_eq, Power.coord1] using hfux
        exact hlu
      · have hxh : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) h := by
          have hvx' : D.lt (Power.coord1 v) (Power.coord1 x) := by simpa using hvx
          have hfxv : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) (Power.coord1 (f.toFun ⟨v, hvI⟩).1) :=
            hdec v x hvI hxI hvx'
          simpa [hv_eq, Power.coord1] using hfxv
        exact hxh
    · intro hx
      rcases hx with ⟨hx_ab, hxI, hfx⟩
      rcases hu_ab with ⟨hau, hub⟩
      rcases hv_ab with ⟨hav, hvb⟩
      have h_lfx : D.lt l (Power.coord1 (f.toFun ⟨x, hxI⟩).1) := by
        simpa [Power.coord1] using hfx.1
      have h_fxh : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) h := by
        simpa [Power.coord1] using hfx.2
      have hxu : D.lt (Power.coord1 x) (Power.coord1 u) := by
        rcases D.trichotomy (Power.coord1 x) (Power.coord1 u) with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
        · exact hlt
        · exfalso
          have hx_equ : x = u := by ext i; fin_cases i; exact heq
          have hll : D.lt l l := by
            have hlu_u : D.lt l (Power.coord1 (f.toFun ⟨u, huI⟩).1) := by
              have hEq_val : (f.toFun ⟨x, hxI⟩).1 = (f.toFun ⟨u, huI⟩).1 := by
                simpa using congrArg (fun z => (f.toFun z).1) (by
                  apply Subtype.ext; exact hx_equ)
              simpa [hEq_val, Power.coord1] using h_lfx
            simpa [hu_eq, Power.coord1] using hlu_u
          exact D.irrefl l hll
        · exfalso
          have hfxu : D.lt (Power.coord1 (f.toFun ⟨x, hxI⟩).1) l := by
            simpa [hu_eq, Power.coord1] using hdec u x huI hxI hgt
          exact D.irrefl l (D.trans h_lfx hfxu)
      have hvx : D.lt (Power.coord1 v) (Power.coord1 x) := by
        rcases D.trichotomy (Power.coord1 v) (Power.coord1 x) with ⟨hlt, _, _⟩ | ⟨heq, _, _⟩ | ⟨hgt, _, _⟩
        · exact hlt
        · exfalso
          have hx_eqv : x = v := by
            ext i
            fin_cases i
            exact heq.symm
          have hhh : D.lt h h := by
            have hcoord_eq : Power.coord1 (f.toFun ⟨x, hxI⟩).1 = h := by
              have hEq : f.toFun ⟨x, hxI⟩ = f.toFun ⟨v, hvI⟩ := by congr
              simp [hEq, hv_eq, Power.coord1]
            simpa [hcoord_eq] using h_fxh
          exact D.irrefl h hhh
        · exfalso
          have hfxv : D.lt h (Power.coord1 (f.toFun ⟨x, hxI⟩).1) := by
            simpa [hv_eq, Power.coord1] using hdec x v hxI hvI hgt
          have hhh : D.lt h h := D.trans hfxv h_fxh
          exact D.irrefl h hhh
      constructor
      · exact by simpa [Endpoint.finite] using hvx
      · exact by simpa [Endpoint.finite] using hxu

lemma construct_local_continuity_witness
    (f : DefinableFunction M I B) (hmono : StrictlyMonotoneOn D I B f.toFun)
    (hDomain : (openInterval D a b).Subset I)
    (hMapsTo : forall x, openInterval D a b x -> exists hx, openInterval D (Endpoint.finite r) (Endpoint.finite s) (f.toFun ⟨x, hx⟩).1)
    (hSurj : forall y, openInterval D (Endpoint.finite r) (Endpoint.finite s) y ->
    exists x, openInterval D a b x /\ exists hx, (f.toFun ⟨x, hx⟩).1 = y)
    (x : Power R 1) (hx_ab : openInterval D a b x)
    (a_var b_var v_var : Power R 1)
    (hGraph : (FunctionGraph f.toFun) (Power.append x v_var))
    (h_av : Lt1 D a_var v_var) (h_vb : Lt1 D v_var b_var) :
    exists c d : Power R 1,
      Lt1 D c x /\ Lt1 D x d /\
      forall y w : Power R 1,
        I y ->
        Lt1 D c y -> Lt1 D y d ->
        (FunctionGraph f.toFun) (Power.append y w) -> Lt1 D a_var w /\ Lt1 D w b_var := by
  rcases hGraph with ⟨hxGraph, hEq⟩
  have hxGraph' : I x := by
    simpa [Power.left_append] using hxGraph
  have hEq' : v_var = (f.toFun ⟨x, hxGraph'⟩).1 := by
    simpa [Power.left_append] using hEq
  rcases hMapsTo x hx_ab with ⟨hxMap, hVal⟩
  have hSubtypeEq : (Subtype.mk x hxMap : {z // I z}) = (Subtype.mk x hxGraph' : {z // I z}) := by
    simp
  have hEqMap : (f.toFun ⟨x, hxMap⟩).1 = v_var := by
    simpa [hSubtypeEq] using hEq'.symm
  rcases (show openInterval D (Endpoint.finite r) (Endpoint.finite s) v_var from by
    simpa [hEqMap] using hVal) with ⟨h_rv, h_vs⟩
  have h_rv' : D.lt r (Power.coord1 v_var) := by simpa using h_rv
  have h_vs' : D.lt (Power.coord1 v_var) s := by simpa using h_vs
  have h_lower_lt_v : D.lt (if D.lt (Power.coord1 a_var) r then r else (Power.coord1 a_var)) (Power.coord1 v_var) := by
    by_cases hlt : D.lt (Power.coord1 a_var) r
    · simpa [if_pos hlt] using h_rv'
    · simpa [if_neg hlt] using (by simpa [Lt1] using h_av)
  obtain ⟨l, h_lower_l, h_lv⟩ := D.dense h_lower_lt_v
  have h_v_lt_upper : D.lt (Power.coord1 v_var) (if D.lt (Power.coord1 b_var) s then (Power.coord1 b_var) else s) := by
    by_cases hlt : D.lt (Power.coord1 b_var) s
    · simpa [if_pos hlt] using (by simpa [Lt1] using h_vb)
    · simpa [if_neg hlt] using h_vs'
  obtain ⟨h, h_vh, h_upper_h⟩ := D.dense h_v_lt_upper
  have h_lh : D.lt l h := D.trans h_lv h_vh
  have h_l_in_rs : D.lt r l /\ D.lt l s := by
    constructor
    · by_cases hlt : D.lt (Power.coord1 a_var) r
      · have h_r_l : D.lt r l := by simpa [if_pos hlt] using h_lower_l
        exact h_r_l
      · have h_a_l : D.lt (Power.coord1 a_var) l := by
          simpa [if_neg hlt] using h_lower_l
        rcases D.trichotomy r (Power.coord1 a_var) with ⟨h_r_a, _, _⟩ | ⟨h_eq, _, _⟩ | ⟨h_a_r, _, _⟩
        · exact D.trans h_r_a h_a_l
        · simpa [h_eq] using h_a_l
        · exact False.elim (hlt h_a_r)
    · exact D.trans h_lv h_vs'
  have h_h_in_rs : D.lt r h /\ D.lt h s := by
    constructor
    · exact D.trans h_rv' h_vh
    · by_cases hlt : D.lt (Power.coord1 b_var) s
      · have h_h_b : D.lt h (Power.coord1 b_var) := by simpa [if_pos hlt] using h_upper_h
        exact D.trans h_h_b hlt
      · have h_h_s : D.lt h s := by simpa [if_neg hlt] using h_upper_h
        exact h_h_s
  obtain ⟨al, be, h_al_be, h_equiv⟩ :=
    preimage_of_open_interval (l := l) (h := h) f hmono hDomain hSurj h_lh h_l_in_rs.1 h_h_in_rs.2
  have h_x_al_be : openInterval D al be x := by
    apply (h_equiv x).mpr
    have hEqDomain : (f.toFun ⟨x, hDomain hx_ab⟩).1 = v_var := by
      have hSubtypeEq' : (Subtype.mk x (hDomain hx_ab) : {z // I z}) = (Subtype.mk x hxGraph' : {z // I z}) := by
        simp
      rw [hSubtypeEq']
      exact hEq'.symm
    have hOut : openInterval D (Endpoint.finite l) (Endpoint.finite h) v_var := by
      constructor
      · simpa using h_lv
      · simpa using h_vh
    exact ⟨hx_ab, ⟨hDomain hx_ab, by simpa [hEqDomain] using hOut⟩⟩
  obtain ⟨c0, d0, h_al_c, hc0x, hd0x, h_d_be⟩ :=
    exists_finite_between_of_extended_interval ⟨h_x_al_be.1, h_x_al_be.2⟩
  let c : Power R 1 := fun _ => c0
  let d : Power R 1 := fun _ => d0
  have hcx : Lt1 D c x := by
    dsimp [c, Lt1]
    exact hc0x
  have hxd : Lt1 D x d := by
    dsimp [d, Lt1]
    exact hd0x
  refine ⟨c, d, hcx, hxd, fun y w hy hcy hyd hGw => ?_⟩
  have hy_al_be : openInterval D al be y := by
    constructor
    · exact lt_of_lt_of_lt_finite h_al_c (by simpa [c] using hcy)
    · exact lt_of_finite_lt_of_lt (by simpa [d] using hyd) h_d_be
  have h_y_lh := (h_equiv y).mp hy_al_be
  have hy' : I y := h_y_lh.2.1
  have h_fy_lh : openInterval D (Endpoint.finite l) (Endpoint.finite h) (f.toFun ⟨y, hy'⟩).1 := h_y_lh.2.2
  have h_w_lh : D.lt l (Power.coord1 w) /\ D.lt (Power.coord1 w) h := by
    rcases hGw with ⟨hy, h_eq⟩
    have h_eq' : w = (f.toFun ⟨y, hy'⟩).1 := by
      rw [← Power.right_append y w]
      rw [h_eq]
      have h_sub : (Subtype.mk (y.append w).left hy : {z // I z}) = Subtype.mk y hy' := by
        apply Subtype.ext
        simp [Power.left_append]
      exact congr_arg (fun z => (f.toFun z).val) h_sub
    have h_fy_lh' := h_fy_lh
    rw [← h_eq'] at h_fy_lh'
    exact h_fy_lh'
  have h_aw : Lt1 D a_var w := by
    dsimp [Lt1]
    have h_a_l : D.lt (Power.coord1 a_var) l := by
      by_cases hlt : D.lt (Power.coord1 a_var) r
      · have h_r_l : D.lt r l := by simpa [if_pos hlt] using h_lower_l
        exact D.trans hlt h_r_l
      · simpa [if_neg hlt] using h_lower_l
    exact D.trans h_a_l h_w_lh.1
  have h_wb : Lt1 D w b_var := by
    dsimp [Lt1]
    by_cases hlt : D.lt (Power.coord1 b_var) s
    · have h_h_b : D.lt h (Power.coord1 b_var) := by
        simpa [if_pos hlt] using h_upper_h
      exact D.trans h_w_lh.right h_h_b
    · have h_h_s : D.lt h s := by
        simpa [if_neg hlt] using h_upper_h
      rcases D.trichotomy (Power.coord1 b_var) s with ⟨h_bs, _, _⟩ | ⟨h_eq, _, _⟩ | ⟨h_sb, _, _⟩
      · exact False.elim (hlt h_bs)
      · rw [h_eq]
        exact D.trans h_w_lh.right h_h_s
      · exact D.trans h_w_lh.right (D.trans h_h_s h_sb)

  exact ⟨h_aw, h_wb⟩

theorem strictly_monotone_definable_continuous_on_subinterval
    (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hmono : StrictlyMonotoneOn D I B f.toFun)
    (a b : Endpoint R) (hab : Endpoint.lt D a b)
    (r s : R) (_hrs : D.lt r s)
    (hDomain : (openInterval D a b).Subset I)
    (hMapsTo : forall x, openInterval D a b x ->
      exists hx : I x,
        openInterval D (Endpoint.finite r) (Endpoint.finite s) (f.toFun ⟨x, hx⟩).1)
    (hSurj : forall y, openInterval D (Endpoint.finite r) (Endpoint.finite s) y ->
      exists x, openInterval D a b x /\
        exists hx : I x, (f.toFun ⟨x, hx⟩).1 = y) :
    exists a b : Endpoint R,
      Endpoint.lt D a b /\
      (openInterval D a b).Subset I /\
      (forall x, openInterval D a b x ->
        ContinuousAtOnGraph D I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun) x) := by
  exact ⟨a, b, hab, hDomain, fun x hx_ab =>
    have hxI : I x := hDomain hx_ab
    ⟨hxI, fun a_var b_var v_var hG h_av h_vb =>
      let ⟨c, d, hcx, hxd, hprop⟩ :=
        construct_local_continuity_witness f hmono hDomain hMapsTo hSurj x hx_ab a_var b_var v_var hG h_av h_vb
      ⟨c, d, hcx, hxd, fun y w hy hcy hdy hGw =>
        hprop y w hy hcy hdy hGw⟩⟩⟩
