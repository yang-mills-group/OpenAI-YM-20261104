import YM.GapsContact.Slab.Along

/-!
# True point Gram inequalities

Schwinger point law of actual operator input includes reflection at time axis, monotonicity; use
as SINGLE budget small & intermediate scales. We expose more exact measurement semantics and
price projection across physical engineering grades. Based on SharpGram.Annulus.Glass (source
in ancestor tree) adapted to `cost`, unselected, complex labels, and true lower-level filtration.
-/

set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Power
open Function Filter Set MeasureTheory Metric Analysis Table Extraction Spec OS Word
open Push.FiniteDetection.Free OPE.Levy Ascent
open scoped Topology BigOperators Classical NNReal InnerProductSpace
variable {G:Gauge}{L:Register G}{T:Table L} (H:T.Hierarchy) (P:DiffPlan T) {d e n:ℕ}{r s:ℝ}

-- generic, adapted to comparator and inherits to slab `cost`.
def chip (d:ℕ) (r:ℝ) (x:T.Field d) : ℝ:= Real.sqrt ‖valTwo T d (r • detectors) x (T.adj H.spin d timeAxis x)‖
lemma chip_nn (d:ℕ)(r:ℝ)(x:T.Field d) : 0≤ chip H d r x:= Real.sqrt_nonneg _

-- OS ordering: right ray in slot 0, left reflected of slot 1; adapted Glass.
def sourceWord (x:L.Ref d)(hr:0<r) : OS.Future L timeAxis:=
  ⟨[((r/2) • basis timeAxis, (⟨d,x⟩:L.Token))],by
    constructor
    · exact Word.locations.mpr (by simp)
    intro v hv; rw [show v= _ from List.mem_singleton.mp hv]; simp; exact hr⟩
lemma detector_in (hr : 0<r) : r • detectors ∈ conf 2 := (Next.UVStress.enlarged hr _).mp detectors_in
lemma psalm (X : OS.Chamber T timeAxis) (hr:0<r) (x y : L.Ref d) :
    T.classMoment T (fun _=>d) (r • detectors) ![T.project d x, T.adj H.spin d timeAxis (T.project d y)] =
      inner ℂ (X.GNS.plant (sourceWord y hr)) (X.GNS.plant (sourceWord x hr)) := by
  let p : Points 2 := r • detectors
  let u := (r/2) • basis timeAxis
  let v := Ortho.move (Signed.reflect timeAxis) u
  let w (y:L.Ref d) :=sourceWord y hr
  let ix : L.Token := ⟨d,x⟩; let iy : L.Token := L.reflectedToken timeAxis ⟨d,y⟩
  let q : Fin 2 → L.Token := fun i=>(⟨d,(![x,L.adj d timeAxis y] : Fin 2→ L.Ref d) i⟩:L.Token)
  rw [X.GNS.measure]
  change _ = T.expect (Word.reflect _ _ ++ _)
  let P := Word.reflect (sourceWord y hr).val timeAxis ++ (sourceWord x hr).val
  have hP : P = [(v,iy),(u,ix)] := by simp [P,v,iy,u,ix,sourceWord,Word.reflectedPoint]
  have hx : Word.distinct P := Word.twoSides (sourceWord y hr).property (sourceWord x hr).property
  have hv : v = -u := by
    unfold u v; ext i; by_cases h:i=timeAxis <;> simp [h,u]
  have hu : u+u=r • basis timeAxis:= by unfold u; rw [← add_smul]; ring_nf
  have he:P.reverse = [(u,ix),(v,iy)] := by rw [hP]; rfl
  have hy: Word.carry P.reverse u=Word.realize q p:=by
    rw [he]; let A : L.Token := ⟨d,L.adj d timeAxis y⟩; have hA: A=iy:=rfl
    simp [p,q,v,detectors,Word.carry,Word.realize,hu,hv,←hA,A, List.ofFn_succ, ix]; rfl -- adjust
  change _=T.expect P
  rw [← Table.order T H.laws.toSymmetric hx (List.reverse_perm P).symm,
      ← OS.invariance H.translations (show Word.distinct P.reverse from Word.locations.mpr (by rw [List.map_reverse,List.nodup_reverse]; exact Word.locations.mp hx)) u,
      hy,T.readAt]
  · rw [adj_project]; let a : Fin 2 → L.Ref d := ![x,L.adj d timeAxis y]; change T.classMoment T _ _ _=T.read p q
    rw [show ![_, T.project d (L.adj d timeAxis y)]=fun i : Fin 2=> T.project d (a i) from funext (fun i=>by fin_cases i <;> rfl)]
    exact T.class_agrees T H.laws.toSymmetric (fun _=>le_rfl) _ (detector_in hr) a

-- Actual Pay.
private def woke (X : OS.Chamber T timeAxis)(hr:0<r)(x:T.Field d) := X.GNS.plant (sourceWord (T.representative d x) hr)
private lemma woken (X:OS.Chamber T timeAxis)(hr:0<r)(x y : T.Field d) :
    inner ℂ (woke X hr x) (woke X hr y)=valTwo T d (r • detectors) y (T.adj H.spin d timeAxis x):= by unfold woke; rw [←psalm H X hr,T.rep,T.rep]; rfl
private lemma psalmed (X:OS.Chamber T timeAxis)(hr:0<r)(x : T.Field d) : chip H d r x=‖woke X hr x‖ := by
   unfold chip; rw [← woken H X hr]
   rw [inner_self_eq_norm_sq_to_K]; change Real.sqrt ‖(↑‖woke X hr x‖:ℂ)^2‖=_; rw [← Complex.ofReal_pow,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]

lemma power_signal (x:T.Field d)(hr:0< r)(hs:r≤ s): chip H d s x≤chip H d r x := by
   obtain ⟨X⟩:= OS.realization H timeAxis
   have hp (v:L.Ref d): sourceWord v (hr.trans_le hs) = OS.travel (sourceWord v hr) ⟨(s-r)/2,div_nonneg (sub_nonneg.mpr hs) zero_le_two⟩:= by
      apply Subtype.ext; unfold OS.travel
      simp only [sourceWord, Word.carry,List.map_cons,List.map_nil]; rw [← add_smul]; change _ = [((r / 2+(s-r)/2) • basis timeAxis, (⟨d,v⟩: L.Token))]; rw [show r / 2+(s-r)/2=s/2 by ring]
   rw [psalmed H X hr, psalmed H X (hr.trans_le hs),woke, hp, X.atBirth]; exact (((X.flow.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (X.flow.shrinks _)))

-- re complex and polarized for currency lower
local instance (d : ℕ) : FiniteDimensional ℝ (T.Field d) := Module.Finite.trans ℂ _

def bond (d:ℕ)(r:ℝ) : T.Field d→ₗ[ℝ] T.Field d→ₗ[ℝ] ℝ:=
   let M:=linear₂ (T.classMoment T (fun _ : Fin 2=>d) (r • detectors))
   let t (x:T.Field d):= T.adj H.spin d timeAxis x
   LinearMap.mk₂ ℝ (fun x y=>(M x (t y)).re)
     (fun y z x=> by rw [map_add, LinearMap.add_apply,Complex.add_re])
     (fun a y z=> by unfold t; rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply]; simp)
     (fun x y z=> by unfold t adj; rw [map_add,map_add,Complex.add_re])
     (fun a x y=> by unfold t adj; rw [← Complex.coe_smul, LinearMap.map_smulₛₗ]; simp)
lemma bonded (r:ℝ)(x y:T.Field d) : bond H d r x y=(valTwo T d (r • detectors) x (T.adj H.spin d timeAxis y)).re := rfl
lemma bond_symm (hr:0<r)(x y:T.Field d): bond H d r x y=bond H d r y x:=by
   obtain ⟨X⟩:=OS.realization H timeAxis; rw [bonded,bonded,← woken H X hr,← woken H X hr]; exact inner_re_symm (𝕜:=ℂ) ..
lemma bond_root (hr:0<r)(x:T.Field d): chip H d r x ^ 2=bond H d r x x:=by obtain ⟨X⟩:=OS.realization H timeAxis; rw [bonded, psalmed H X hr,← woken H X hr]; exact (_root_.inner_self_eq_norm_sq (𝕜:=ℂ) (woke X hr x)).symm
lemma bond_cs (hr:0<r)(x y:T.Field d): bond H d r x y ≤ chip H d r x * chip H d r y := by
   obtain ⟨X⟩:=OS.realization H timeAxis; rw [bonded, psalmed H X hr,psalmed H X hr,← woken H X hr]; exact le_trans (Complex.re_le_norm _) ((norm_inner_le_norm _ _).trans_eq (mul_comm ..))
lemma chip_add (hr:0<r)(x y:T.Field d): chip H d r (x+y)≤chip H d r x+chip H d r y:=by
   apply (sq_le_sq₀ (chip_nn ..) (add_nonneg (chip_nn ..) (chip_nn ..))).mp; rw [bond_root H hr,add_sq,map_add]; simp only [LinearMap.add_apply,map_add,← bond_root H hr,bond_symm H hr y x]
   nlinarith only [bond_cs H hr x y]
lemma chip_smul (c:ℂ)(r:ℝ)(x:T.Field d): chip H d r (c • x)= ‖c‖*chip H d r x:=by
  let M:=linear₂ (T.classMoment T (fun _ : Fin 2=>d) (r • detectors))
  have he : T.adj H.spin d timeAxis (c • x)=star c • T.adj H.spin d timeAxis x:= by unfold adj; rw [LinearMap.map_smulₛₗ]; rfl
  unfold chip; rw [he]
  change Real.sqrt ‖M (c • x) (star c • T.adj H.spin d timeAxis x)‖ = ‖c‖*Real.sqrt ‖M x (T.adj H.spin d timeAxis x)‖
  rw [M.map_smul,LinearMap.smul_apply,(M x).map_smul,norm_smul,norm_smul,norm_star,← mul_assoc,← sq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (norm_nonneg _)]
lemma chip_zero (r:ℝ):chip H d r 0=0:=by simpa using chip_smul (d:=d) H 0 r 0
lemma chip_neg (r:ℝ)(x:T.Field d):chip H d r (-x)=chip H d r x:=by simpa using chip_smul H (-1) r x
lemma chip_cont (d:ℕ)(r:ℝ)(hr:0<r):Continuous (chip H d r):=by
   let M (x:T.Field d):= LinearMap.toContinuousLinearMap (bond H d r x)
   let P:T.Field d →ₗ[ℝ] T.Field d →L[ℝ] ℝ:={ toFun:=M,map_add':=fun x y=> ContinuousLinearMap.ext fun v=>LinearMap.congr_fun ((bond H d r).map_add x y) v,map_smul':=fun a y=> ContinuousLinearMap.ext fun v=>LinearMap.congr_fun ((bond H d r).map_smul a y) v }
   rw [show chip H d r=fun x=>Real.sqrt (P x x) from funext fun x=> by change _=Real.sqrt (bond H d r x x); rw [← bond_root H hr,Real.sqrt_sq (chip_nn ..)]]; exact Continuous.sqrt ((show Continuous P from P.continuous_of_finiteDimensional).clm_apply continuous_id)

-- climb lower field precisely. useful for limits of true transitions
-- borrowed part: direct for first via SharpGram/Weak/Compatible. Adapt for constructor
-- without SharpGram.Monolith use own form.
def knot (T:Table L) (d:ℕ)(p: Points 2)(y:T.Field e): T.Field d →ₗ[ℂ] ℂ:= Work.A15.front p (![⟨e,y⟩] : Fin 1→T.Tag) _
lemma knotted (p:Points 2)(x:T.Field d)(y:T.Field e): knot T d p y x=T.useAt T p ![⟨d,x⟩,⟨e,y⟩]:=Work.A15.front_apply p ..
lemma knot_val (p:Points 2)(x y:T.Field d): knot T d p y x=valTwo T d p x y:=by
  rw [knotted]; let q : Fin 2 → T.Tag := fun i=> ⟨d,(![x,y] : Fin 2→T.Field d) i⟩
  rw [show (![⟨d,x⟩,⟨d,y⟩] : Fin 2→T.Tag)=q from funext (fun i=>by fin_cases i <;> rfl)]; rfl
lemma knot_lift (h:P.Inclusions T)(hd:d≤e)(p:Points 2)(hp:p∈conf _)(x:T.Field d)(y:T.Field n): knot T e p y (P.rise hd x)=knot T d p y x:=by
  rw [knotted,knotted]; exact h.kernels _ _ hp _
lemma bond_inherit (h:P.Inclusions T)(h₀:P.Orientation H.spin)(hd:d≤e)(hr:0<r)(x y:T.Field d):
   bond H d r x y=bond H e r (P.rise hd x) (P.rise hd y):=by
  rw [bonded,bonded,← knot_val,←knot_val,knot_lift P h hd _ (detector_in hr),knotted,knotted]
  have he:T.adj H.spin e timeAxis (P.rise hd y)= P.rise hd (T.adj H.spin d timeAxis y):=by simp [Table.adj,h₀.realInc,h₀.mirrorInc]
  let p : Equiv.Perm (Fin 2):= Equiv.swap 0 1
  have hp (x y:T.Tag): ![x,y] ∘ p=![y,x] := by funext i; fin_cases i <;> simp [p]
  rw [he,← Table.class_perm T T H.laws.toSymmetric p (detector_in hr), hp,
      ← Table.class_perm T T H.laws.toSymmetric p (detector_in hr) ![⟨d,x⟩,(⟨e,P.rise hd (T.adj H.spin d timeAxis y)⟩: T.Tag)],hp]; apply congr_arg
  exact (h.kernels hd _ (Points.rearrange_in p (detector_in hr)) ![⟨d,x⟩]).symm
lemma chip_inherit (h:P.Inclusions T)(h₀:P.Orientation H.spin)(hd:d≤e)(hr:0<r)(x:T.Field d): chip H d r x=chip H e r (P.rise hd x):=by
   apply (sq_eq_sq₀ (chip_nn ..) (chip_nn ..)).mp; rw[bond_root H hr,bond_root H hr,bond_inherit H P h h₀ hd hr]

lemma paid_coin {C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(d:ℕ)(r:ℝ)(x:S.Field d): cost F d r x=chip F.room.kernel d r x:= rfl
end YM.GapsContact.Power
