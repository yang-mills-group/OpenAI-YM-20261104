import YM.OPE.Compatible.Turbine.Shovel
/-! Strip the restored level, after its cost at the *entire* frontierCoefficient term. -/
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
local notation "K₁"=> fun (d:ℕ) i=> shortInk D U p₀ u (s i) d
local notation "K₂"=>fun (d n:ℕ)i=> tallInk D U p₀ u (s i) d n
-- signed mixed, at exact d for entire levels
local notation "C!" => fun i c=> frontierCoefficient D T K! c (s i) (x i)
local notation "S!"=> fun i c => shoot D T U u c (s i) (x i) p
variable (c':Tones T)
local notation "ℜ"=> fun i=>trunc T d (s i u) (picked Θ (x i)) (picked Θ p) (x i u)
local notation "ℜ'"=> fun i=>shadow P d (picked Θ (x i)) (picked Θ P₀) (x i u)
local notation "k"=> c'.fst
local notation "M'"=> shades (facets T)
local notation "q"=>fun (z:S.Field d)=>update p u (⟨d,z⟩: S.Tag)
-- product sums
variable {v f' f'' : I→ ℝ} {w₁ w₂:I→ℂ}
lemma PaidWeight.accrue (h:PaidWeight φ r f' w₁)(he:PaidWeight φ r f'' w₂)(hf:∀ᶠ i in φ, v i=f' i*f'' i): PaidWeight φ r v (fun i=> w₁ i*w₂ i):=by
    refine ((show Score .. from h).product (show Score .. from he)).congr ?_
    filter_upwards [hf] with i hi; rw [hi,norm_mul]; ring
lemma PaidWeight.summon {X':Type}(S:Finset X') (g':X'→ I→ℂ) (hr:Tendsto r φ atTop)(hh:∀ᶠ i in φ, 0≤ v i) (h:∀ i∈ S, PaidWeight φ r v (g' i)) : PaidWeight φ r v (fun i=>∑ j∈S,g' j i):=by
    apply (_root_.YM.OPE.PaidWeight.ascaled hh).2; simp_rw [Finset.smul_sum]; exact Score.summar _ _ hr fun i hi => (PaidWeight.ascaled hh).1 (h i hi)
include A H' hM Y hO hη hu hx
lemma standing (y:Tones T): PaidWeight φ r (fun i=>leverage D U p₀ u (s i) y.fst k) (fun i=> S! i y*C! i c' (paint T u p y)):=
   PaidWeight.accrue (glen_bill D T u p hu Y H' hO A hη hM hx y) (prime_load D T u p hu Y H' hO A hη hM hx c' (title T y)) (Eventually.of_forall (fun i=>reloaded D u P₀ _ _ (s i)))
include hh ht -- find P
lemma final_tour (hh':d+1≤ b): PaidWeight φ r (fun i=>leverage D U p₀ u (s i) (d+1) k) (fun i=> frontierCoefficient D T U c' (s i) (x i) p-∑ i'∈ M' d,S! i i'* C! i c' (paint T u p i')):=by
    let W:= M' d; let W':= M' (d+1); let J:=fun i':Tones T=>fun i=> S! i i'* C! i c' (paint T u p i') -- name conflict remove
    obtain ⟨P,hP⟩:=Prescription.chosen T.room.kernel.laws.toSymmetric T.phase.transport.injection
    let v:= fun i=> leverage D U p₀ u (s i) (d+1) k; have he:∀ᶠ i in φ, 0 ≤ v i:= (atProfits D u P₀ (n:=k) (d:=d+1) hu Y).mono fun i hi=>hi.1.le; have hr:=Burst.life D Y
    have hg:= PaidWeight.summon (W' \ W) J hr he (fun i hi=>by
       have hh:= standing D T u p hu Y H' hO A hη hM hx c' i
       obtain ⟨h1,h2⟩:=Finset.mem_sdiff.mp hi; have ht: i.fst=d+1:= le_antisymm ((shadows ..).1 h1) (Nat.add_one_le_iff.mpr (lt_of_not_ge (mt ((shadows ..).2) h2)))
       simp_rw [ht] at hh; exact hh)
    refine ((tower_pays D T P u p hu Y H' hO A hP hη hM hh hh' ht hx c').add hg he hr).alter ?_
    filter_upwards with i; change _-(∑ j∈ W',J j i)+(∑ j∈W'\W,J j i)=_-(∑ j∈W,J j i); rw [← Finset.sum_sdiff (show W ⊆ W' from fun i hi=> (shadows ..).2 (((shadows ..).1 hi).trans d.le_succ))]; abel
end YM.OPE.Arboreal.Trace
