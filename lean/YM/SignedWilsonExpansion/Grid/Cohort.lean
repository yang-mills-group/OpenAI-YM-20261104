import YM.SignedWilsonExpansion.Grid.Fair
import YM.SignedWilsonExpansion.TwoGrid
namespace YM.SignedWilsonExpansion.Overlap.Cohort
/-! Phase shells with magnetic-plane pair probe. Project the *fixed* axis
    partial port, not an angular claim in all spacetime. Fair π twice spatially (price over transverse Mag p and p3). -/
set_option autoImplicit false
noncomputable section
open Function Set MeasureTheory Filter Finset
open MS MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.Plane.Wire MS.High MS.Tone
open Energy (leg)
open FVA2 FVA2.Lambda Area HighRank HighScale Walk AxisChoice
open MassShift MarkShift Align Fair
open FourierGaussian (axis)
open scoped Classical Topology ContDiff BigOperators
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "Z" => Momentum.sq
local notation "η" => FourierGaussian.jump

local notation "R" => Fair.cost
local notation "π" => Fair.price
local notation "X" => Fair.mix
variable (p:FourP) (m:Bool)
local notation "Q" => fun p u => Energy.leg (degreeX m) 2 u p
local notation "e" => Align.vane m
local notation "T" => Align.tune m
local notation "g" => Energy.called (degreeX (!m)) 2
variable {G:Gauge}{B:MS.Land.Booked (Press.portDeck G)}(M:MS.Land.MS_Data G B)(simple:G.Simple) (v:ℝ) (a:G.ColorIndex)
local notation "K" => MarkShift.settled M (g G) v
local notation "L" => K (0,0)
local notation "β" => (v*Align.salaryQ G)
local notation "Y" => (P×P)
-- Polarization exists, extracted on pair chart; using form EXACTLY, not just on radial finite nodal jets.
section price_mark
abbrev Bi := (Y) →ₗ[ℝ] (Y) →ₗ[ℝ] ℂ
variable (k:P)
private lemma forms (f:Y→ℂ)(hf:Shape f (2:ℤ)) : ∃ T':Bi,∀ p:Y, f p=T' p p:= by
    let H:Tensor.T Y ℂ 2:= Tensor.coeff f 2 0; let V':=H.toMultilinearMap.curryLeft; let s:=MultilinearMap.ofSubsingletonₗ ℝ ℝ Y ℂ (0:Fin 1)
    refine ⟨ s.symm.toLinearMap.comp V',?_ ⟩ -- use simp? explicit
    intro p; obtain hx:= congr_fun ( hf.form (j:=2)) p; apply hx.trans; change H (fun _=>p)=H (Fin.cons p (fun _=>p)); congr 1; funext i; fin_cases i <;> rfl
include simple
lemma settled_shape (i j:Axis) : ∃ B:Bi,∀ k p, L [ W i a k,W j a p]= B (k,p) (k,p):= by
   let w: Wire (Branch G Axis) Y P := [ (W₀ i a,ContinuousLinearMap.fst ℝ P P),(W₀ j a, ContinuousLinearMap.snd ℝ P P) ]; have hh: Shape (fieldVal L w) (2:ℤ):= ( Align.static2 M simple v (!m)|>.form ) 0 0 _ (fun h=> Bool.noConfusion h) rfl
   obtain ⟨b,h⟩:= forms _ hh; exact ⟨b,fun k p=>h (k,p)⟩
lemma flipNorm (i j:Axis): L [W i a (-p), W j a (-k)]= L [ W i a p, W j a k ]:= by obtain ⟨b,h⟩:= settled_shape m M simple v a i j; rw [ h,h,← Prod.neg_mk, map_neg,map_neg,LinearMap.neg_apply, neg_neg ] -- order?
omit simple
lemma mean_Z (i:Bool) (f:P→ₗ[ℝ]ℂ): π p (fun p=> (Q p (e i)) • f p) =( R p/2:ℝ ) • f (T i):= Fair.monAd p m i f
local notation "V" => ( P → ℂ )
lemma price_s (f:V): π p f=(∑ i: Fair.I,f (Fair.mix i p))/12:=rfl
-- shorthand independent contraction on mixed term
abbrev L₂ (b:Bi) := LinearMap.compl₁₂ b (LinearMap.inl ℝ P P) (LinearMap.inr ℝ P P)
lemma joint (b:Bi)(i j:Bool) :
      π p (fun p=> π k (fun k=> Q k (e i) • Q p (e j) • b (k,p) (k,p)))=
           (R k*R p/4:ℝ) • ( b (T i,0) (0,T j) + b (0,T j) (T i,0) ):= by
    let A:= L₂ b + L₂ b.flip; let S(k:P):=b (k,0) (k,0); let V'(p:P):= b (0,p) (0,p)
    have hx(k p:P): b (k,p) (k,p)= S k+ A k p+V' p:= by
       rw [show ((k,p):Y)= (k,0)+(0,p) from (by ext <;> simp) ]; simp only [ map_add,LinearMap.add_apply]; change _=b _ _+(b _ _+ b _ _)+ b _ _; simp only [LinearMap.inl_apply,LinearMap.inr_apply]; abel -- might goals unresolved
    have hu (p:P)(x:Bool)(c:ℂ): π p (fun p=> Q p (e x) • c)=0:= by simp_rw [ price_s,← Finset.sum_smul,Fair.mon0 ]; simp only [zero_smul,zero_div]
    let Q0 (x:Bool):P→ℝ:= fun k=> Q k (e x); let C:= π k (fun k=> Q0 i k • S k)
    have he (r:P):π k (fun k=> Q0 i k • Q0 j r • b (k,r) (k,r))= Q0 j r • C+ Q0 j r • ((R k/2:ℝ) • A (T i) r):= by
       simp_rw [ hx ]; have ht: (fun k=>Q0 i k • Q0 j r • (S k+A k r+V' r)) = Q0 j r • ((fun k=>Q0 i k • S k)+(fun k=> Q0 i k • (A.flip r k)) +(fun k=> Q0 i k • V' r)):= by funext k; simp only [ smul_add,Pi.add_apply,Pi.smul_apply,LinearMap.flip_apply ]; rw [smul_comm, smul_comm (Q0 i k),smul_comm (Q0 i k)] -- coding
       rw [ht, show ∀ (x:V)(t:ℝ), π k ( t • x ) = t • π k x from (fun x t=> map_smul ( (π k).restrictScalars ℝ ) ..), map_add,map_add, hu k i (V' r),mean_Z k m i (A.flip r),add_zero,smul_add ]; rfl
    change π p (fun p=> π k (fun k=> Q0 i k • Q0 j p • b (k,p) (k,p))) =_
    simp_rw [he]; rw [show (fun p=> _)= (fun p=> Q0 j p • C)+(fun p=> Q0 j p • ((( R k/2:ℝ ) • A (T i)) p)) from ?_, map_add, hu p j C, mean_Z p m j ((R k/2:ℝ) • A (T i)),zero_add,LinearMap.smul_apply, smul_smul ]; swap; · rfl
    change (R p/2*(R k/2) :ℝ) • _ = (R k*R p/4:ℝ) • A (T i) (T j); congr 1; ring
lemma holy (_:Y)(b:Bi)(k p:P) : (1/2:ℝ) • ( b (k,p) (k,p)-b (k,-p) (k,-p) )= b (k,0) (0,p)+b (0,p) (k,0):= by
    rw [show ((k,p):Y)=(k,0)+(0,p) from (by ext <;> simp), show ((k,-p):Y)=(k,0)-(0,p) from (by ext <;> simp) ]; simp only [map_add,map_sub, LinearMap.add_apply, LinearMap.sub_apply]; module
include simple
lemma session (x y:Bool):
    π p (fun p=>π k (fun k=> (Q k (e x)) • (Q p (e y)) • L [ W (e x) a k, W (e y) a p ] ))=
       (R k*R p/4:ℝ) • ((1/2:ℝ) • (torch 2 L [W (e x) a (T x),W (e y) a (T y)]- torch 2 L [ W (e x) a ( T x ), W (e y) a ( -T y ) ] )):= by
    obtain ⟨b,h⟩:= settled_shape m M simple v a (e x) (e y)
    rw [ OrderHigh.stamp_static (Align.static2 M simple v (!m)) _ _ (fun h=>Bool.noConfusion h) _ rfl rfl,
         OrderHigh.stamp_static (Align.static2 M simple v (!m)) _ _ (fun h=>Bool.noConfusion h) _ rfl rfl ]; simp_rw [h]; rw [joint,holy (k,p)]
omit simple
lemma shiftBool (c:Axis→ℂ):
    (∑ i:Axis, (Q p i) • c i)=∑ i:Bool, (Q p (e i)) • c (e i):= by
   cases m <;> ( rw [TwoGrid.card4]; simp (disch:=decide) [Energy.leg, Align.vane, degreeX]; abel)

lemma total_rank (a:P)(b:P)(f:Axis→Axis→ℂ):
     (∑ i:Axis, ∑ j:Axis, Q a i • Q b j • f i j )=∑ i:Bool, ∑ j:Bool,Q a (e i) • Q b (e j) • f (e i) (e j):= by
    simp_rw [ ← Finset.smul_sum, shiftBool]; -- outer?
lemma sale {A:Type}(s:Finset A)(z:A→FourP→ℂ): π p (fun p=>∑ i∈s,z i p) =∑ i∈s,π p (z i):= by rw [ ← map_sum ]; exact congr_arg (π p) (funext fun p=> ( Finset.sum_apply .. ).symm) -- under lambda?
include simple
abbrev escrow (A:G.ColorIndex)(k p:P):ℂ:= ∑ i:Axis, ∑ j:Axis, Q k i • Q p j • L [ W i A k,W j A p ] -- parse hidden
lemma counted:
     π p (fun p=>π k (fun k=> escrow m M v a k p))=↑( (-2*β*R k*R p:ℝ) ):= by
    have hp : Align.tested a m L=( (-8:ℂ)* ( ↑( β ) :ℂ) ):= by
       have he:= Align.pay_value M simple a v (!m); rw [ Bool.not_not ] at he; exact he
    have hx : (R k* R p / 4:ℝ) • Align.tested a m L= ↑( ( -2*β*R k*R p:ℝ) ):= by rw [hp,Complex.real_smul ]; push_cast; ring
    unfold escrow; simp_rw [ total_rank, sale k, sale p, session p m M simple, ← hx ]; unfold Align.tested; simp_rw [ Finset.smul_sum ]
end price_mark
end
end YM.SignedWilsonExpansion.Overlap.Cohort
