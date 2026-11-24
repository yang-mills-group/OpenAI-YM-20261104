import YM.LocalLTE.XPre.Lamp
import YM.MergeProof.Cashew
import YM.MergeProof.Tuna
/-!
# Agenda recording entire analytic leaf costs and currency through
actual retained stamp. Label pin density QA.Later consumes this with
T.Tunes for grouped leaves and with perturbative horizons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ K ν t u q r s b:ℝ} {A:Activities G f} {d p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations
variable {v w:ℂ}{X:Wing→Prop}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
local notation "F₁"=> Config G f→ ℂ
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
-- cost t bounds both.E. Additional Magn lane.F.H v Unit costs.
-- Excluded cost ψB only Nonread.Answer permits closed log.Frame. Δ from shifting Beacon.
def Reader (R:Rep G f) (d:ℕ)(κ:ℝ)(p l:ℕ)(M:Leaf R): Prop:=∃ g, Lamp R d κ p l M g
noncomputable def tollNon (A:ι→Prop)(M:ι→Leaf R)(g:ι→ℂ)(i:ι):ℝ:= if A i then 0 else ‖g i‖*load (M i)
structure Circuit (X: Wing→Prop)(L:GaugeDoor R C) (d:ℕ)(κ:ℝ)(p l:ℕ) (o:Site f)(o':Site c)(v:ℂ)(E:Config G f→ ℂ) (Z:Res G f)(W:Res G c)(w:ℂ)(t u b:ℝ): Prop where
   lamps : ∃ (ι:Type)(_ : Countable ι) (M:ι→ Lotus.Leaf R)(g:ι→ℂ)(φ:MergeProof.Response G c)(P:ι→Prop), Odyssey X o o' v E Z W w t u L M g φ ∧ SumBudget (tollNon P M g) b ∧ ∀ i,P i→ Reader R d κ p l (M i)
variable (h:Circuit X L d κ p l o o' v E Z W w t u b)
set_option quotPrecheck false
local notation "tn"=> tollNon
-- record witness used later by industry.Letter
include h
lemma widened {Y:Wing→Prop}(hp:t≤r)(hx:u ≤q)(hQ:X≤Y)(he:b ≤ s): Circuit Y L d κ p l o o' v E Z W w r q s:=by
   obtain ⟨I,hI,M,g,ψ,A,h,hx',hM⟩:= h.lamps; exact ⟨_,hI,M,g,ψ,A,h.elevate hQ hp hx,budget_loosen hx' he,hM⟩
lemma scalar_t (c:ℂ) : Circuit X L d κ p l o o' v (c • E) (c • Z) (c • W) (c*w) (‖c‖*t) (‖c‖*u) (‖c‖*b):=by
    obtain ⟨I,hI,M,g,φ,A,h,hv,hM⟩:= h.lamps; refine ⟨I,hI,M, c • g, c • φ,A,h.quaver c,?_,hM⟩
    have ht:= budget_scale (norm_nonneg c) hv; convert! ht using 1; ext j; unfold tollNon; split <;>simp [mul_assoc]
lemma corpo_transport (c d':ℂ)(he:c=v*d'): Circuit X L d κ p l o o' 1 (c • E) (c • Z) (d' • W) (c*w) (‖c‖*t) (‖d'‖*u) (‖c‖*b):=by
    obtain ⟨I,hI,M,g,φ,A,h,hv,hM⟩:= h.lamps; refine ⟨I,hI,M, c • g, d' • φ,A,?_ ,?_,hM⟩
    · have hz:=h.quaver c
      refine ⟨hz.member,hz.purchase,stack_of h.cost d',hz.lyric,hz.old,fun i V=>?_⟩
      simp_rw [hook_scale, Pi.smul_apply, smul_eq_mul, ← mul_sub]; refine ((h.grants i V).mul_left d').congr_fun (fun i=>?_); rw [he]; ring
    have ht:= budget_scale (norm_nonneg c) hv; convert! ht using 1; ext j; unfold tollNon; split<;>simp [mul_assoc]
section
variable (m:Motion) (a : Site c) (T:R.activities.Moves m.1 (S.ratio.embed a))(hs:SoundDoor S L)(ht:Menu.Tunes L)
-- Motion preservation for all tokens.E hanger.Even zero plates. Φ needs growth power receipts.Zoom all.
local notation "aa" => S.ratio.embed a
local notation "A₀"=> rotationP ((YM.Labels.frames G).level d) (R.p.order) (R.p.power)
local notation "Ie" F => Leaf.route T F
omit h
variable {l':ℝ}(hY:1≤l')
include ht
lemma respected (M:Leaf R) i (U : Config G c) : L.hinge (prized l' hY M) i U=L.hinge M i U:=by
    let F:= prized l' hY M; let N:Unit→Leaf R:=fun _=>M; let k(_:Unit):ℝ:=1
    have h : Merge.Grouped F k N:=by refine ⟨fun i=> rfl,Summable.of_finite, fun i=>?_⟩; simp [k,N,F,prized]
    simpa only [k,N,tsum_fintype,Fintype.sum_unique,one_mul] using! (ht _ _ _ _ h i U |>.tsum_eq.symm)
include hs h ht
lemma turning (hr : ConnectedActivityE6.Reliable G κ K)(hv:scalar m v=v): Circuit (Set.image (Wing.labelRoute T) X) L d κ p l (affine m.1 (S.ratio.embed a) o) (affine m.1 a o') v (stepUp m aa E) (floatUp m aa Z) (floatUp m a W) (scalar m w) (A₀*t) u (A₀*b):=by
   obtain ⟨I,hI,M,g,φ,A,h,hv',hM⟩:=h.lamps; let Zx:= Wing.labelRoute T
   let f:=(Leaf.route T ∘ M); let V:=A₀; let g' i:= scalar m (g i); have hP(i): ‖g' i‖= ‖g i‖:= Motion.norm_scalar ..
   have ht0:1 ≤ V:= River.rotation_one ..; let P:= prized V ht0 ∘ f; have he(i): P i = prized V ht0 (Leaf.route T (M i)):= rfl
   have htV(i): load (P i)= V * load (f i):=by
      unfold P load BudgetPoint.mass; change Real.exp _*(V*(f i).weight)=V*(Real.exp _*(f i).weight); exact mul_left_comm ..
   have hk(j): ‖g' j‖*load (P j)= V*(‖g j‖*load (M j)):=by rw [htV, hP,show load (f j) = _ from fareSky m _ T _,mul_left_comm]
   have hv:= h.dancing m a hs T hv; refine ⟨I,hI,P,g',upwards m a φ,A,?_,?_, fun i hi=>?_⟩
   · refine ⟨hv.member,?_,hv.cost,hv.lyric,hv.old, fun j U=> (hv.grants j U).congr_fun fun i=>?_⟩
     · simp_rw [hk]; exact budget_scale (zero_le_one.trans ht0) h.purchase
     change _ * _ * quoted L (P i) j U=_ * _ * quoted L (f i) j U
     simp_rw [show quoted L (P i)= _ from (show quoted L (P i) = quoted L (f i) from congr_arg (profile C.activities) (funext fun k=> funext fun U=>Complex.ofReal_inj.mpr (respected ht ht0 (f i) k U)))]; rfl -- orientation.F
   · have hg:=budget_scale (zero_le_one.trans ht0) hv'; convert! hg using 1; ext j; unfold tollNon; split
     next h=> rw [mul_zero]
     next h=> rw [hk]
   obtain ⟨e,he⟩:= hM i hi; exact ⟨_,carrying d m aa T he hr⟩
end
omit h
variable {f':ι→ Config G f→ℂ}{Z₀:ι→Res G f}{W₀:ι→Res G c}{a:ι→ ℂ}{V T U:ι→ℝ}
lemma bandR [Countable ι](hs:SoundDoor S L)(h:∀ i:ι, Circuit X L d κ p l o o' v (f' i) (Z₀ i) (W₀ i) (a i) (V i) (T i) (U i)) (hp:∀ i,HasSum (fun j=>f' j i) (E i))(hq:∀ i Y, HasSum (fun j=>Z₀ j i Y) (Z i Y))(hr:∀ i Y, HasSum (fun j=>W₀ j i Y) (W i Y))(he:HasSum a w)(ht: SumBudget V t)(hu: SumBudget T u)(hx:SumBudget U b) : Circuit X L d κ p l o o' v E Z W w t u b:=by
    choose I hI M g φ Qx hG hv hrT using fun i=> h i|>.lamps; exact ⟨_,inferInstance,Sigma.uncurry M,Sigma.uncurry g,MergeProof.band φ,Sigma.uncurry Qx,symbolize L hs hG hp hq hr he ht hu,sumBudget_sigma hv hx,fun i=> hrT i.1 i.2⟩
end YM.LocalLTE.XPre
