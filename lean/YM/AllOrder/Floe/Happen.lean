import YM.AllOrder.Floe.Merit
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent
variable (Γ:ι→ℝ) {q:Clip} {R:ι→PathData G}{L:ι→ℝ}(h : ∀ i,(R i).Bounds q a C (L i)) (g:G.Simple) {s:Fees} (t:Age) {T: Age→ ι→ℝ} {H:ι→Scene G}(p:Age→ℕ)(α:ι→ℝ)
local notation "p≀"=> fun (i:Age)=> gateE (p i) N
local notation "X"=> Age.scope (k+2)
local notation "Z"=> Age.scope (rank k)
variable {σ:Fees}{V:ι→Layout G}{Q:ι→ Coin} (h0:0≤Ω) (hh : ∀ i∈ Age.scope N,Rent.Spirit Γ q R H s i a C (σ i) Ω (p i) N (T i))
variable (A : Sustained Γ p α N s H R T k q V Q) (hp: ∀ i,0<s i)(hC: CreditF Γ 1 L)(hg:Aligned p N)(hT:∀ i∈Age.scope N,CreditF Γ (gateE (p i) N+1) (T i))(hα:Pace.Cost Γ 1 α)(hV:∀ i, Pace.Valid (H i) N)
-- issue maybe typo.
include hp A
include hT hg h h0 hh hV hC hα g
local notation "L'"=> upto k
variable (hτ: Step.rank k ≤ N)
include hτ
lemma aptE :∃ V Q,Sustained Γ p α N s H R T (k+1) q V Q:= by
 let π:= rank k; choose f η φ hβ hΨ hφ using (fun (i:Age)(hi:i∈upto k)=> obtain_call Γ h g p α h0 hh A hp hC hg hT hα hV hτ i hi)
 let V' :ι→Layout G:=fun j i => if h:i∈upto k then f i h j else V j i
 have hc (i:Fin (k+4)): entry k i∈ upto k:=Finset.mem_image_of_mem _ (Finset.mem_univ i); let b(i:Fin (k+4)) j:= η (entry k i) (hc i) j
 let Q' :ι→ Coin:= fun i=>Function.update (Q i) π (b 0 i); have hh j (i:Age)(hi:i∈X):V' j i= V j i:= dif_neg (fun hZ=> Finset.disjoint_left.mp (fresh_set k) hZ hi)
 have ht i (x:ℕ)(hx:x<π):Q i x=Q' i x:= Eq.symm (Function.update_of_ne hx.ne _ _); have he (i:ι): Earn (Q' i) (α i):= by
     unfold Earn; rw [← ht i 0 (by unfold π Step.rank; omega),← ht i 1 (by unfold π Step.rank; omega),← ht i 2 (by unfold π Step.rank; omega)]; exact A.due i
 refine ⟨V',Q', ⟨?_,?_,he,fun j i hi=>?_,?_⟩⟩
 · intro i hi; change i∈Step.tape π at hi; obtain h|h:= Finset.mem_union.mp ((revealed k).symm ▸ hi); swap; · obtain ⟨f,hz,hf⟩:= A.rents i h; exact ⟨f,hz,fun j=> (hh j i h).symm ▸ hf j⟩
   refine ⟨φ i h,hΨ i h,fun j=>?_⟩; rw [show V' j i= f i h j from dif_pos h]; exact (hφ i h j).1
 · intro i hi; obtain he|rfl:= lt_or_eq_of_le (Nat.le_of_lt_succ hi); · rw [show (fun h=>Q' h _)= _ from (show (fun h=> Q' h (rank i))=(fun h=>Q h (rank i)) from funext (fun h=> (ht h _ (by unfold π rank; omega)).symm))]; exact A.income i he
   rw [show (fun j=>Q' j (rank i))=b 0 from funext (fun _=> Function.update_self ..)]; exact hβ (entry i 0) (hc 0) -- rewrite case maybe substitutes k
 · exact (Function.update_of_ne (show i ≠ π by unfold π rank; omega) _ (Q j)).trans (A.dormant j i (by omega)) -- arg order
 intro i j; refine readout q (R i) (h i) g (H i) (V i) (V' i) (fun x=> b x i) (supports Γ p α A hp i) (hh i) (he i|>.1) (A.calls i j) (hV i) hτ (ht i) ?_ ?_ -- edit args.
 · change Q' i π= Q i π+b 0 i; rw [show Q' i π=b 0 i from Function.update_self ..,A.dormant i π (le_refl _),zero_add]
 intro x; unfold V'; rw [dif_pos (hc x)]; exact (hφ (entry k x) (hc x) i).2
omit A hτ in
-- low book proof later.N fixed≥2.P.Price allowance.
lemma resume (V:ι→Layout G)(Q:ι→ Coin)(hA:Sustained Γ p α N s H R T 0 q V Q)(h':k+2≤N): ∃ F Q,Sustained Γ p α N s H R T k q F Q:= by
 induction k with
 | zero=> exact ⟨V,Q,hA⟩
 | succ i ih=> obtain ⟨U,Q',hQ⟩:= ih (by omega); exact aptE Γ h g p α h0 hh hQ hp hC hg hT hα hV h'
end YM.AllOrder.Floe.Step
