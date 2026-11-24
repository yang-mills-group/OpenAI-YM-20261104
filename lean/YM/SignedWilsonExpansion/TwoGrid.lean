import YM.SignedWilsonExpansion.FourierGaussian
namespace YM.SignedWilsonExpansion.TwoGrid
/-! Phase shells with magnetic-plane pair probe. Project the *fixed* axis
    partial port, not an angular claim in all spacetime. Use C4 twice independently. -/
set_option autoImplicit false
noncomputable section
open Function Set MeasureTheory Filter Finset
open MS MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.Plane.Wire MS.High MS.Tone
open Energy (leg)
open FVA2 FVA2.Lambda Area HighRank HighScale Walk AxisChoice
open FourierGaussian (axis)
open scoped Classical Topology ContDiff BigOperators
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "Z" => Momentum.sq
local notation "η" => FourierGaussian.jump
local notation "Q" => (fun p u => Energy.leg 1 2 u p)
local notation "Ω" => AxisChoice.disk
local notation "τ" => Tone.bill
variable (d:ℝ)(p:P)
-- rotate1 swaps plane axes and negates entrance 1.
abbrev tr (z:ℝ)(i:Axis):ℝ:= if i=1 then -z else z
def move (p:FourP):FourP:=fun i:Axis=> tr (p ((Equiv.swap 1 2) i)) i
lemma move_p : move p=![p 0,-p 2,p 1,p 3]:= by funext i; fin_cases i <;> simp [move,tr,Equiv.swap_apply_def]; -- time convention
lemma keeps : MeasurePreserving move μ μ:= by
    let e:=(MeasurableEquiv.arrowCongr' (Equiv.swap (1:Axis) 2) (MeasurableEquiv.refl ℝ))
    let g:P→P:=fun p i=> tr ( p i ) i
    have hv:MeasurePreserving g volume volume:= by
       apply volume_preserving_pi (f:=fun i p=>tr p i); intro i; by_cases he:i=(1:Axis); · simp_rw [tr, he,if_true]; exact Measure.measurePreserving_neg volume
       simp_rw [tr, if_neg he]; exact MeasurePreserving.id _
    have hT : move=g ∘ e:= rfl
    have he: MeasurePreserving move volume volume:= by
       rw [hT]; exact hv.comp ( volume_preserving_arrowCongr' (Equiv.swap (1:Axis) 2) (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _) )
    exact ⟨he.measurable,by rw [ show μ=_ from (show μ= ENNReal.ofReal Gaussian.capμ • volume from Gaussian.land), Measure.map_smul, he.map_eq ] ⟩
lemma measureIt : MeasurableEmbedding move:= by
    refine Measurable.measurableEmbedding ?_ ?_ -- standard polish
    · exact keeps.measurable
    intro x y h; simp_rw [ move_p ] at h; funext i; fin_cases i <;> simp_all
abbrev turns (i:Axis) (k:P) := move^[i.val] k
lemma travel (i:Axis): MeasurePreserving (turns i) μ μ := keeps.iterate i.val
lemma travelE (i:Axis): MeasurableEmbedding (turns i):= by
    -- turns.elim
    suffices h:∀ n:ℕ,MeasurableEmbedding (move^[n]) from h _
    intro n; induction n with | zero=> exact MeasurableEmbedding.id | succ n ih=> exact ih.comp measureIt
local notation "⊞" k ":" f => turns f k -- not
local notation "e" => AxisChoice.direction
local notation "T" => AxisChoice.tangent
lemma card4 : Finset.univ (α:=Axis)= {0,1,2,3}:=rfl
lemma trcD (i:Axis): Ω (turns i p)= Ω p:= by fin_cases i <;> simp (disch:=decide) [AxisChoice.disk,turns,move_p,iterate_succ_apply'] <;> ring
lemma trcB (i:Axis): Z (turns i p)= Z p:= by unfold Momentum.sq; rw [card4]; fin_cases i <;> simp (disch:=decide) [turns,move_p,iterate_succ_apply'] <;> ring
lemma trcN (i:Axis): turns i (-p)= -(turns i p):= by funext k; fin_cases i <;> norm_num [turns,move,tr,Equiv.swap_apply_def,iterate_succ_apply'] <;> split_ifs <;> simp
lemma trcF (i:Axis): τ (axis d) (turns i p)=τ (axis d) p:= by simp_rw [ FourierGaussian.bill_act ]; congr 1; fin_cases i <;> simp (disch:=decide) [turns,move_p,iterate_succ_apply']
lemma flow_trc (x:Bool): ∑ i:Axis,Q (turns i p) (e x)=0:= by rw [card4]; cases x <;> simp (disch:=decide) [turns,move_p,iterate_succ_apply',direction,Energy.leg] <;> ring
lemma disk_trc (x:Bool): (∑ i:Axis, Q (turns i p) (e x) • turns i p)= (2 * Ω p :ℝ) • T x:= by
    rw [card4]; funext u; fin_cases u <;> cases x <;> simp (disch:=decide) [turns,move_p,iterate_succ_apply',direction,Energy.leg,AxisChoice.disk,AxisChoice.tangent,unitV,spike,Pi.single_apply] <;> ring

local notation "V" => (P→ℂ)
def price (k:P) : (FourP→ℂ) →ₗ[ℂ] ℂ where
   toFun f:= (∑ i:Axis, f (turns i k))/4
   map_add' f g:= by simp only [Pi.add_apply, Finset.sum_add_distrib,add_div]
   map_smul' c f:= by simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul,Finset.mul_sum,mul_div_assoc, ← Finset.mul_sum  ]
local notation "π" => price
lemma price_s (f:V): π p f= (∑ i:Axis,f (turns i p))/4:=rfl
lemma uniform {f:V}{p:P}{c:ℂ}(h:∀ i:Axis,f (turns i p)=c): π p f=c:= by rw [price_s]; simp_rw [h,Finset.sum_const]; norm_num [Axis]
lemma currency {f:V}{p:P}{c:ℂ}(h:∀ i:Axis,f (turns i p)=c)(g:V): π p (fun q=> f q*g q)=c*π p g:= by simp_rw [price_s,h,← Finset.mul_sum, mul_div_assoc]
lemma commutes (f:P→P→ℂ)(k:P): π p (fun q=>π k (fun l=> f l q))=π k (fun l=>π p (fun q=> f l q)):= by simp_rw [price_s,← Finset.sum_div]; rw [Finset.sum_comm]
lemma antip {f:V}: π p (fun q=> f (-q))=π (-p) f:= by simp only [price_s,trcN]
lemma rotate_int {f:V}(h:Integrable f μ): Integrable (fun p=> π p f) μ:= by simp_rw [price_s]; exact (integrable_finsetSum _ fun i _=> ((travel i).integrable_comp_emb (travelE i) ).mpr h).div_const _
lemma count_int {f:V}(h: Integrable f μ): ∫ k:FourP,π k f ∂μ=∫ k:FourP,f k∂μ := by
    simp_rw [price_s]; rw [ integral_div, integral_finsetSum _ ( fun i _=> show Integrable (fun k=>f (turns i k)) μ from ((travel i).integrable_comp_emb (travelE i)).mpr h ) ]; simp_rw [ (travel _).integral_comp (travelE _) f,sum_const ]; norm_num [Axis]
lemma costs_mean (f:P→P→ℂ)(h:∀ t, Integrable (fun k=> f t k) μ) : price p (fun q=>∫ k,f q k∂μ) = ∫ k, price p (fun q=> f q k)∂μ:= by
    simp_rw [price_s]; rw [ integral_div, integral_finsetSum _ (fun i _=> h _) ]
-- contraction density e μ. Exterior and closed-loop both averaged for double probe.
local notation "g" => Energy.called 1 2
variable {G:Gauge}{B:MS.Land.Booked (Press.portDeck G)}(M:MS.Land.MS_Data G B)(simple:G.Simple) (v:ℝ) (a:G.ColorIndex)
local notation "K" => MarkShift.settled M (g G) v
local notation "L" => K (0,0)
local notation "β" => (v*OrderHigh.locus G)
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
   let w: Wire (Branch G Axis) Y P := [ (W₀ i a,ContinuousLinearMap.fst ℝ P P),(W₀ j a, ContinuousLinearMap.snd ℝ P P) ]; have hh: Shape (fieldVal L w) (2:ℤ):= ( OrderHigh.static_M M simple v|>.form ) 0 0 _ (fun h=> Bool.noConfusion h) rfl
   obtain ⟨b,h⟩:= forms _ hh; exact ⟨b,fun k p=>h (k,p)⟩
lemma flipN (i j:Axis): L [W i a (-p), W j a (-k)]= L [ W i a p, W j a k ]:= by obtain ⟨b,h⟩:= settled_shape M simple v a i j; rw [ h,h,← Prod.neg_mk, map_neg,map_neg,LinearMap.neg_apply, neg_neg ] -- order?
omit simple
lemma mean_Z (i:Bool) (f:P→ₗ[ℝ]ℂ): price p (fun p=> (Q p (e i)) • f p) =( Ω p/2:ℝ ) • f (T i):= by
   simp_rw [ ← map_smul, price_s, ← map_sum,disk_trc ]; simp_rw [ map_smul, Complex.real_smul ]; push_cast; ring
-- shorthand independent contraction on mixed term
abbrev L₂ (b:Bi) := LinearMap.compl₁₂ b (LinearMap.inl ℝ P P) (LinearMap.inr ℝ P P)
lemma joint (b:Bi)(i j:Bool) :
      price p (fun p=> price k (fun k=> Q k (e i) • Q p (e j) • b (k,p) (k,p)))=
           (Ω k*Ω p/4:ℝ) • ( b (T i,0) (0,T j) + b (0,T j) (T i,0) ):= by
    let A:= L₂ b + L₂ b.flip; let S(k:P):=b (k,0) (k,0); let V'(p:P):= b (0,p) (0,p)
    have hx(k p:P): b (k,p) (k,p)= S k+ A k p+V' p:= by
       rw [show ((k,p):Y)= (k,0)+(0,p) from (by ext <;> simp) ]; simp only [ map_add,LinearMap.add_apply]; change _=b _ _+(b _ _+ b _ _)+ b _ _; simp only [LinearMap.inl_apply,LinearMap.inr_apply]; abel -- might goals unresolved
    have hu (p:P)(x:Bool)(c:ℂ): price p (fun p=> Q p (e x) • c)=0:= by simp_rw [ price_s,← Finset.sum_smul,flow_trc ]; simp only [zero_smul,zero_div]
    let Q0 (x:Bool):P→ℝ:= fun k=> Q k (e x); let C:= price k (fun k=> Q0 i k • S k)
    have he (r:P):price k (fun k=> Q0 i k • Q0 j r • b (k,r) (k,r))= Q0 j r • C+ Q0 j r • ((Ω k/2:ℝ) • A (T i) r):= by
       simp_rw [ hx ]; have ht: (fun k=>Q0 i k • Q0 j r • (S k+A k r+V' r)) = Q0 j r • ((fun k=>Q0 i k • S k)+(fun k=> Q0 i k • (A.flip r k)) +(fun k=> Q0 i k • V' r)):= by funext k; simp only [ smul_add,Pi.add_apply,Pi.smul_apply,LinearMap.flip_apply ]; rw [smul_comm, smul_comm (Q0 i k),smul_comm (Q0 i k)] -- coding
       rw [ht, show ∀ (x:V)(t:ℝ), π k ( t • x ) = t • π k x from (fun x t=> map_smul ( (π k).restrictScalars ℝ ) ..), map_add,map_add, hu k i (V' r),mean_Z k i (A.flip r),add_zero,smul_add ]; rfl
    change price p (fun p=> price k (fun k=> Q0 i k • Q0 j p • b (k,p) (k,p))) =_
    simp_rw [he]; rw [show (fun p=> _)= (fun p=> Q0 j p • C)+(fun p=> Q0 j p • ((( Ω k/2:ℝ ) • A (T i)) p)) from ?_, map_add, hu p j C, mean_Z p j ((Ω k/2:ℝ) • A (T i)),zero_add,LinearMap.smul_apply, smul_smul ]; swap; · rfl
    change (Ω p/2*(Ω k/2) :ℝ) • _ = (Ω k*Ω p/4:ℝ) • A (T i) (T j); congr 1; ring
lemma holy (S:Y)(b:Bi)(k p:P) : (1/2:ℝ) • ( b (k,p) (k,p)-b (k,-p) (k,-p) )= b (k,0) (0,p)+b (0,p) (k,0):= by
    rw [show ((k,p):Y)=(k,0)+(0,p) from (by ext <;> simp), show ((k,-p):Y)=(k,0)-(0,p) from (by ext <;> simp) ]; simp only [map_add,map_sub, LinearMap.add_apply, LinearMap.sub_apply]; module
include simple
lemma session (x y:Bool):
    price p (fun p=>price k (fun k=> (Q k (e x)) • (Q p (e y)) • L [ W (e x) a k, W (e y) a p ] ))=
       (Ω k*Ω p/4:ℝ) • ((1/2:ℝ) • (torch 2 L [W (e x) a (T x),W (e y) a (T y)]- torch 2 L [ W (e x) a ( T x ), W (e y) a ( -T y ) ] )):= by
    obtain ⟨b,h⟩:= settled_shape M simple v a (e x) (e y)
    rw [ OrderHigh.stamp_static (OrderHigh.static_M M simple v) _ _ (fun h=>Bool.noConfusion h) _ rfl rfl,
         OrderHigh.stamp_static (OrderHigh.static_M M simple v) _ _ (fun h=>Bool.noConfusion h) _ rfl rfl ]; simp_rw [h]; rw [joint,holy (k,p)]
omit simple
lemma shiftBool (c:Axis→ℂ):
    (∑ i:Axis, (Q p i) • c i)=∑ i:Bool, (Q p (e i)) • c (e i):= by rw [card4]; simp [Energy.leg,direction,Axis,add_comm]
lemma total_rank (a:P)(b:P)(f:Axis→Axis→ℂ):
     (∑ i:Axis, ∑ j:Axis, Q a i • Q b j • f i j )=∑ i:Bool, ∑ j:Bool,Q a (e i) • Q b (e j) • f (e i) (e j):= by
    simp_rw [ ← Finset.smul_sum, shiftBool]; -- outer?
lemma sale {A:Type}(s:Finset A)(z:A→FourP→ℂ): π p (fun p=>∑ i∈s,z i p) =∑ i∈s,π p (z i):= by rw [ ← map_sum ]; exact congr_arg (π p) (funext fun p=> ( Finset.sum_apply .. ).symm) -- under lambda?
include simple
abbrev escrow (A:G.ColorIndex)(k p:P):ℂ:= ∑ i:Axis, ∑ j:Axis, Q k i • Q p j • L [ W i A k,W j A p ] -- parse hidden
lemma counted:
     price p (fun p=>price k (fun k=> escrow M v a k p))=↑( (-2*β*Ω k*Ω p:ℝ) ):= by
    unfold escrow; simp_rw [ total_rank, sale k, sale p ]; rw [ ← show (Ω k*Ω p/4:ℝ) • AxisChoice.probeAct a L=↑( (-2*β*Ω k*Ω p:ℝ) ) from ?_ ]; swap; · rw [OrderHigh.mark_money M simple, Complex.real_smul]; push_cast; ring
    unfold AxisChoice.probeAct; simp_rw [ Finset.smul_sum, session _ M simple ]
end price_mark
end
end YM.SignedWilsonExpansion.TwoGrid
