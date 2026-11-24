import YM.OPE.Compatible.Turbine.Lube
/-! Recover real coordinates. Gain from the precise expenditure certified above. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I J' : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives)(u:X)
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "K!"=> Arboreal.trim U u
local notation "H"=>brim D (Arboreal.trim U u)
local notation "V"=>brim D U
local notation "Θ"=>glen D U u
variable (p:X→ S.Tag)(hu:u∈ rest U){b d:ℕ}{φ:Filter I}{s:I→X→ℝ}{r f:I→ℝ}
variable [Fintype J'] (z:I→J'→E4)(w:J'→ S.Tag)(t:I→Viewers T)
variable (Y:Burst D U φ r s){η M c:ℝ}(H':Services C Λ S)(hO:Lanes (F:=Λ) T.sector.derivatives) (A: Allot C)(h:P.Coherent)
variable (a:Mode T.sector.derivatives) (hη:0 < η)(hM:0 ≤ M)(hc:0<c) (hh:1 ≤ b)(hb:d ≤ b)
variable (ht:∀ᶠ i in φ, whenHigh U (schedule C b (η/2) (s i))=schedule C b (η/2) (s i) u∧ aperture D C b 2 (η/2) (r i) (s i) u ≤ schedule C b (η/2) (s i) u-1)
variable {x:I→X→E4} (hx:∀ᶠ i in φ,Ridge (s i) η M D U (away (x i) (x i ⊥)))
local notation "O!" => fun i=> x i ⊥
local notation "X!"=> fun i=>away (x i) (x i ⊥)
local notation "Z!"=>fun i=>away (z i) (x i ⊥)
local notation "p₀"=> fun i:V=>(p i.val).1
local notation "K₀"=> fun (n:ℕ) i=> leverage D U p₀ u (s i) d n
local notation "P₀"=> Ward.expose ∘ p
variable (hy:∀ᶠ i in φ, ClearOf (x i ⊥) (z i) c)
local notation "V₀"=> picked V
local notation "P!"=> P.ope
local notation "g"=>fun (b:Mode L) i=> P.ope b (picked Θ (x i)) (picked Θ (Ward.expose∘p)) (x i u)
local notation "q!"=> fun b: Mode L=> update p u (⟨d,P.loaded b d⟩: S.Tag)
local notation "tr'"=>fun (D':Finset X) (n:ℕ) i (p₁:X→S.Tag)=> shadow P n (picked (brim D D') (x i)) (picked (brim D D') (Ward.expose∘p₁)) (O! i)
local notation "Z" => fun n i => tr' U n i p-∑ b'∈bands L d,g b' i • tr' K! n i (q! b')
local notation "R!"=> fun (Q:Finset X) i (w:X→ S.Tag) (n:ℕ) => ray T n (picked (brim D Q) (x i)) (picked (brim D Q) w) (O! i)
include hη hu A H' hO h hM Y hx hh hb ht
lemma torque : PaidWeight φ r (K₀ a.fst) (fun i => (R! U i p a.fst)-(∑ b'∈ bands L d,g b' i • R! K! i (q! b') a.fst) - Z a.fst i):=by
    have hp:= Burst.crown D Y; obtain ⟨he,hI⟩ := finish_view D Y hx hη (Finset.Subset.refl U) hp
    obtain ⟨hv,hA⟩:= finish_view D Y hx hη (Finset.filter_subset ..) (remains U hp ((rest_mem ..).mp hu|>.1)); let B:= bands L d
    refine PaidWeight.alter (allotted T (z:=fun i=>Z a.fst i) (O!) (fun i=>picked V (x i)) (fun i=>picked H (x i)) (fun _=>picked V p) (fun (b: B) _=> picked H (q! b.val)) (fun (b:B) i=>g b.val i) (Burst.life D Y) ((atProfits D u P₀ (d:=d) (n:=a.fst) hu Y).mono fun i hi=>hi.1.le) he hI hv hA ?_) ?_
    · intro N hn w y δ hδ hY; apply (printed_east D T P u p hu y w Y H' hO A h a hη hM hδ hh hb ht hx hY).alter
      filter_upwards with i; congr 2; exact (Finset.sum_coe_sort B _).symm
    filter_upwards with i; congr 2; exact Finset.sum_coe_sort B (fun b=> g b i • R! K! i (q! b) a.fst)
lemma piston (w:Tones T) : PaidWeight φ r (K₀ w.fst) (fun i=> (legends T).readIn w.fst w (Z w.fst i)):=by
    let R:= (legends T).readIn w.fst w; let n:=w.fst; have he:∀ᶠ i in φ,0 ≤ K₀ n i:= (atProfits D u P₀ (d:=d) (n:=n) hu Y).mono fun _ h=>h.1.le
    let f (i:I) (a: Mode L) := P.ope a (picked V (x i)) (picked V P₀) (O! i); let f' (i:I) (b a :Mode L):= P.ope a (picked H (x i)) (picked H (Ward.expose ∘ (q! b))) (O! i); let c i a := f i a- ∑ b∈ bands L d,g b i*f' i b a
    have hv (i:I): R (Z n i)= ∑ a∈bands L n,c i a • R (P.loaded a n):=by
       dsimp only; have ht: Z n i= ∑ a∈ bands L n, c i a • P.loaded a n:= by
           unfold c; change (∑ a∈bands L n,f i a • P.loaded a n)-(∑ b∈bands L d,g b i • ∑ a∈bands L n,f' i b a • P.loaded a n)=_ -- precedence
           simp_rw [sub_smul,Finset.sum_smul,mul_smul,Finset.smul_sum,Finset.sum_sub_distrib]
           rw [Finset.sum_comm (s:=bands L d) (t:=bands L n)]
       change R (Z n i)=_; rw [ht,map_sum]; exact sum_congr rfl fun _ _=> map_smul ..
    apply (PaidWeight.ascaled he).2; change Score φ r (fun i=> (↑(K₀ n i):ℂ) • R (Z n i)); simp_rw [hv, Finset.smul_sum]
    apply Score.summar _ _ (Burst.life D Y); intro a ha; have ha:= (full_bands ..).1 ha; rcases ha.eq_or_lt with ha|ha
    · have hh:= printed_west D T P u p hu Y H' hO A h a hη hM hh hb ht hx; rw [ha] at hh; refine (((PaidWeight.ascaled he).1 hh).dot (Score.steady (R (P.loaded a n)) (Burst.life D Y))).congr ?_; exact Eventually.of_forall fun i=>smul_assoc ((K₀ n i:ℝ):ℂ) (c i a) _
    have hb:R (P.loaded a n)=0:= readFZero T w a P ha; simp_rw [hb,smul_zero]; exact Score.steady _ (Burst.life D Y)
lemma vehicle (w:Tones T) : PaidWeight φ r (K₀ w.fst) (fun i=>frontierCoefficient D T U w (s i) (x i) p - ∑ c∈ bands L d, g c i *frontierCoefficient D T K! w (s i) (x i) (q! c)):=by
    let R:= (legends T).readIn w.fst w; let n:=w.fst; have he:∀ᶠ i in φ,0 ≤ K₀ n i:= (atProfits D u P₀ (d:=d) (n:=n) hu Y).mono fun _ h=>h.1.le
    have hg:=Burst.life D Y; obtain ⟨a,ha⟩:=exact_grade T P h w
    have Ht:= torque D T P u p hu Y H' hO A h a hη hM hh hb ht hx; rw [ha] at Ht
    apply ((Ht.applyLinear he hg R R.continuous_of_finiteDimensional).add (piston D T P u p hu Y H' hO A h hη hM hh hb ht hx w) he hg).alter
    have hU:=Y.fresh _ hη; have hr := hU.fade _ hU.crowned.base
    filter_upwards [Display.later (I:=↥V) T w hr, Display.later (I:=↥(brim D (Arboreal.trim U u))) T w hr] with i hi hv
    change R (_ - _ - _) + R _ = _; rw [map_sub,sub_add_cancel,map_sub,map_sum]
    unfold frontierCoefficient; simp_rw [map_smul,hv,hi]; rfl
end YM.OPE.Arboreal.Trace
