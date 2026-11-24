import YM.AllOrder.Floe.Aurora
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
variable (F:Forest S.ratio)(P:Layout G)(A:Finset Age)(i:Age)
local notation "Y"=>Poll.Body (Precision.Key F G)
local notation "X"=>Apex c G×Y
local notation "E"=>ℝ×X
variable {α:Type*}{L:Finset α}{R:PathData G}{p:Clip}{o:ChartRatio G}{t:S.Choices}
variable {B:ℝ→ Config G f→ℝ}
variable (V:Desk F o B t) (hp:Legal A P)
open PertExtension GaussianScore
local notation "q"=> fderiv ℝ V.quiet 0
local notation "U"=>Impulse (q) V.high V.paid
local notation "U₁"=> books F P A V
variable (l:Finset Age)
local notation "u"=> books F P l V
local notation "d"=> castle V.hard V.quiet V.pay.steer
section fares
variable {R':Type} [NormedAddCommGroup R'][NormedSpace ℝ R'] [FiniteDimensional ℝ R'] {u₀ V':R'→ℝ}
lemma breakR (h:Rank R' k u₀)(ht:k<j): Radial.jet u₀ j=0:= by
 ext x; rw [← jet_entry (h.read.smooth.contDiffAt.of_le le_top)]; exact (rank_taylor (h.lead (ContinuousLinearMap.toSpanSingleton ℝ x))).1 j ht
lemma jet_minus (h:Plausible u₀)(H:Plausible V')(k:ℕ) : jet (u₀-V') k=jet u₀ k-jet V' k:=by rw [sub_eq_add_neg,sub_eq_add_neg]; ext1 x; rw [jet_add h.smooth.contDiffAt (show ContDiffAt ℝ ω (-V') 0 from H.smooth.contDiffAt.neg)]; simp [jet,iteratedFDeriv_neg_apply]
end fares
namespace Age
def before (i j:Age): Prop:= i.e<j.e ∨ i.e=j.e∧j.r < i.r
abbrev prereq (i:Age) (A:Finset Age):= A.filter (fun j=> before j i)
lemma clock (hf:i∈A): i∉ i.prereq A:= by simp [before,prereq]
lemma prem : i.prereq A⊆A:= filter_subset ..
lemma lesser (hf:j < i.e):∀ x:Age,x.e=j → x∈A → x∈i.prereq A:= fun _ he hv=> Finset.mem_filter.mpr ⟨hv,Or.inl (he.trans_lt hf)⟩ -- u binder notation shadows
lemma s_pair (hF:i∈A)(x:Age)(hx:x∈A)(he:x ∉ i.prereq A)(h:x≠i):i.e < x.e ∨ i.e=x.e ∧ x.r < i.r:= by
 have h':¬ before x i:= fun h=> he (mem_filter.mpr ⟨hx,h⟩); unfold before at h'; push_neg at h'; obtain ⟨a,H⟩:= h'; rcases lt_or_eq_of_le a with hz|hz; exact Or.inl hz; refine Or.inr ⟨hz,lt_of_le_of_ne (H hz.symm) ?_⟩; rintro e; subst_vars; obtain ⟨x,s,t⟩:=x; obtain ⟨a,W,H⟩:=i; exact h (by congr; exact Nat.add_right_cancel hz.symm; exact Nat.add_right_cancel e) -- subst_vars risk
end Age
local notation "R₀" => i.prereq A
include hp
variable (hi:i∈A)
include hi
lemma orders (x:Age)(hx:x∈A)(hv:x∉R₀):i.e≤x.e:= by by_contra! hh; exact hv (mem_filter.mpr ⟨hx,Or.inl hh⟩)
lemma tickets : Legal (R₀) P:= legal_less P A hp R₀ (Age.prem A i)
local notation "Xr"=> books F P (R₀) V
local notation "L₀"=> note_n (i:=i) F P V i.e
set_option quotPrecheck false
local notation "K₀"=> (EuclideanSpace.basisFun (Precision.Key F G) ℝ).toBasis
lemma strict_rank : Rank X (i.r-1) ((U₁ i.e-Xr i.e)+L₀):= by
 let v:= R₀; let B':= A\insert i v; have hhx:A=(insert i v)∪B':=by symm; apply union_sdiff_of_subset; exact Finset.insert_subset hi (Age.prem A i) -- check
 let M z:= note_n (i:=z) F P V i.e; have he':U₁ i.e= U i.e- (M i+(∑ j∈v,M j)+ (∑ j∈B',M j)):= by
    rw [amber F P A V hp i.e, show ∑ j∈A,M j= _ from ?_] -- rw .. fails
    nth_rw 1 [hhx]; rw [Finset.sum_union disjoint_sdiff, sum_insert (i.clock A hi)]; -- signature clock
 have hf j (hj:j∈B'): Rank X (i.r-1) (M j):= by
    obtain ⟨hj,hf⟩:= mem_sdiff.mp hj; obtain ⟨hl,hv⟩:= not_or.mp (mt mem_insert.mpr hf); rcases i.s_pair A hi j hj hv hl with hh|⟨hq,hk⟩
    · unfold M; rw [frost_at _ P A V hp hj hh]; exact Rank.nil _ 0
    unfold M; rw [lush _ P A V hp hj hq.ge, hq,Nat.sub_self, Nat.zero_add]; exact ((Haiku.Project.maturity _ _).lead _).up (by omega)
 rw [he',amber F P (R₀) V (tickets P A i hp hi) i.e]; change Rank X _ ((_-(M i+ (∑ j∈v,_)+(∑ j∈B',_)) - (U i.e-∑ j∈v,_))+ _);
 convert (Rank.sum hf).neg using 1; unfold M v; abel
lemma advances : Rank (Apex c G) (i.r-1) ((Response.distilled (augment F P A V hp) i.e-Response.distilled (augment F P (R₀) V (tickets _ _ _ hp hi)) i.e)+ L₀ ∘ (fun x:Apex c G=> (x,(0:Y)))):= by
 let f':= booked (d) volume U₁ i.e; let g':= booked (d) volume Xr i.e
 have HR:= strict_rank F P A i V hp hi
 have hl: Rank X i.r (L₀):= by rw [lush _ _ A _ hp hi (le_refl i.e),Nat.sub_self,Nat.zero_add]; exact (Haiku.Project.maturity _ _).lead _
 have hk : Rank X i.r (U₁ i.e-Xr i.e):=(add_sub_cancel_right (U₁ i.e-Xr i.e) L₀) ▸ (((HR.up (by omega)).sub hl))
 have hz := unbent (d) K₀ volume («u»:=U₁) (v:=Xr) (win0 _) (win0 _) (fun j=>impulse_rank ..) (fun j=>impulse_rank ..) (fun k hk=> precede F P A V hp _ (i.prem A) (orders _ _ _ hp hi) hk) (by unfold Age.e; omega) hk
 let L:= ContinuousLinearMap.inl ℝ (Apex c G) Y
 convert (((hz.up (by omega)).add HR).lead L) using 1
 ext1 x; change connected (d) volume U₁ i.e x - connected (d) volume Xr i.e x + _= (f' _ - g' _ - _)+_; rw [← final_hot (d) volume («u»:=U₁) (win0 _) (fun i=>impulse_rank ..),← final_hot (d) volume («u»:=Xr) (win0 _) (fun i=>impulse_rank ..)]; change f' (L x)-g' (L x)+ L₀ (L x)=(f' (L x) -g' (L x) - (U₁ i.e (L x)-Xr i.e (L x))) + ((U₁ i.e (L x)-Xr i.e (L x))+ L₀ (L x)); abel
end YM.AllOrder.Floe
