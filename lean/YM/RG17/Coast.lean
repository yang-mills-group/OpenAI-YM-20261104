import YM.RG17.Mooring
import YM.RG17.Avenue
/-!
# Supports from moor from B any such frames. Q choices unrestricted
apart from Sized, Shift duties. Now loc and height and Pegs solidarity
actual. md distance for Lane. Does not verify enough above measuring range
of ALL p. Does NOT verify these Frames ARE the physical frames wished
by WilsonX.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace RG12
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Final C f S}
   {u:Filter (ℕ×ℕ)} (U:Lenses.Mantle F u) (L Y:Layout F)(E:Services C f S)
set_option quotPrecheck false
local notation "H"=> C.path.levels.clock.hatBeta
local notation "a"=> C.S.a
local notation "ρ"=> OPE.run
structure Moors (L Y:Layout F)(n:ℕ) : Prop where
    peg : Pegs U L
    first : Moored C L.level
    frames : L.frame=Y.frame
    charts : L.charts=Y.charts
    sized : Sized C n Y.level
variable {n:ℕ}
include E
lemma granary (h:Moors U L Y n)(d:ℕ) : ∀ᶠ r in home,
   (∀ v:Free C d, ∃ w:C.label d,mass C d w ≤ 2* H (Y.level r) ^(2*Lenses.price d+2*(n+1)*(d+1))* ‖v‖∧
       engineering Y.charts d (Y.level r) w = Y.frame d r v) ∧
   (∀ w:C.label d, ‖(Y.frame d r).symm (engineering Y.charts d (Y.level r) w)‖ ≤
       2* Lenses.bonus C d * H (Y.level r)^(4*(d+1)) * mass C d w ) := by
    have hp:= h.peg; have ht:=h.frames; have hM:=h.charts
    filter_upwards [engineeringPass U L E hp d, bequeath E hp.level h.sized h.first, hp.level.growing.eventually_ge_atTop (C.ref d), h.sized.rank.eventually_ge_atTop (C.ref d)] with r hu hr h0 h1
    let k:=L.level r; let m:=Y.level r; let P:= H k; let Q:= H m
    obtain ⟨hh,hy,he⟩:=hr
    have hx:(1:ℝ)≤Q:= (C.path.levels.fits.delayed _).le
    have hn:P ≤ Q^2:=hh
    constructor
    · intro v; obtain ⟨w,hb,hV⟩:= hu.1 v
      obtain ⟨y,hY,hw⟩:= tread L E hy (one_le_pow₀ hx) w h0 h1
      refine ⟨y,hY.trans ?_,by rw [← ht,← hM,hw,hV]⟩
      let j:=2*(n+1); let t:=Lenses.price d
      change (Q^j)^(d+1)*mass C d w≤ 2*Q^(2*t+j*(d+1))*_
      have hc:mass C d w ≤ 2*(Q^2)^t* ‖v‖ := hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (C.path.levels.fits.delayed k).le) hn _) zero_le_two) (norm_nonneg _))
      apply (mul_le_mul_of_nonneg_left hc (pow_nonneg (pow_nonneg (zero_le_one.trans hx) _) _)).trans_eq
      rw [pow_add Q (2*t),pow_mul Q 2 t,pow_mul Q j (d+1)]; ring
    intro w; obtain ⟨x,hx',hw⟩:= tread L E he (one_le_pow₀ hx) w h1 h0; rw [← hM,← hw, ← ht]
    refine (hu.2 _).trans ((mul_le_mul_of_nonneg_left hx' (mul_nonneg zero_le_two ?_)).trans_eq ?_)
    · unfold Lenses.bonus; positivity
    rw [pow_mul]; simp only [mul_assoc]

omit E
-- For any q n. Don't conflate charts, frame, costs with actual end coefficients.
def row (L:Layout F) (q:ℝ→ℕ) (Z:∀ d:ℕ, ℝ→ C.label d≃ₗ[ℂ] C.label d) :Layout F:={ L with level:=q,shift:=Z }
lemma seaport (hp:Pegs U L) (hm:Moored C L.level) {q} (ht:Sized C n q) (Z:∀ d:ℕ, ℝ→ C.label d≃ₗ[ℂ] C.label d) : Moors U L (row L q Z) n:= ⟨hp,hm,rfl,rfl,ht⟩
variable {U L Y}
include E
lemma stability {n:ℕ} (h:Moors U L Y n)(hy:Located L)(P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (p:ShiftBack Y)
    (hb:∀ d, RateLE home OPE.run (fun r=> (Y.shift d r).toContinuousLinearEquiv.toContinuousLinearMap) 0)
    (hz:∀ᶠ r in home,Y.shift 0 r (C.labels.level 0).e0=(C.labels.level 0).e0): Located Y:=by
    refine byGrade P Y (h.sized.reach ..) p hz ?_ ?_ hb ?_
    · rw [← h.frames]; exact hy.unit
    · rw [← h.frames]; exact hy.nested
    rw [← h.frames]; intro d v j; exact inputUpper P L E hy _ _ (Sum.inr v)

lemma carried (h:Moors U L Y n) {m:ℕ}{d:Fin m→ℕ}(w:(i:Fin m)→Free C (d i)):
    ∃ x:ℝ→ (i:Fin m)→ C.label (d i),∀ᶠ r in home,
    (∀ i, YM.RG17.Paid Y r (x r) i ≤ 2*H (Y.level r)^(2*Lenses.price (d i)+2*(n+1)*(d i+1))* ‖w i‖) ∧
      ∀ i, master Y (d i) r (x r i)= Y.frame (d i) r (w i):=by
   have he: ∀ᶠ r in home, ∀ i:Fin m, ∃ x:C.label (d i), mass C _ (Y.shift (d i) r x) ≤ 2*H (Y.level r)^(2*Lenses.price (d i)+2*(n+1)*(d i+1))* ‖w i‖∧
       master Y _ r x=Y.frame (d i) r (w i):=by
     filter_upwards [eventually_all.mpr (fun i=> granary U L Y E h (d i))] with r hr i
     obtain ⟨x,hx,Hx⟩:= (hr i).1 (w i)
     obtain ⟨y,rfl⟩:= (Y.shift (d i) r).surjective x; exact ⟨y,hx,Hx⟩
   rw [eventually_iff_exists_mem] at he; obtain ⟨K,hK,he⟩:=he
   choose! x hx hv using fun r i (h:r∈K)=>he r h i
   exact ⟨x, mem_of_superset hK (fun r hr=> ⟨fun i=>hx r i hr,fun i=>hv r i hr⟩)⟩
end YM.RG17
