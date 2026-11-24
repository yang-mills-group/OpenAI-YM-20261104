import YM.QuadraticLocal.Germ.Harper
import YM.QuadraticLocal.Shelter.Animal
import YM.QuadraticLocal.Germ.Scribe
/-!
## Audit all analytic model outputs on their normalized stencil valuations

Not scalar-after-many sums; every log term even allocated globally. This accounts for
analytic side ONLY. Kernel and receipt fixed first. Costs as in Earn.Render and Blend
on these supports. Φ test space of input model in each geometric orientation supplies
FULL audit for every v and all kernel paths; additional structures (beyond φ assignments paid
at these supports) must be budgeted before supplying even here.

 Test parameter may be canonical full mood or any rectangle of `𝕜` functions with
 gauges; Aura.Clock later uses this after ℝ-pose and projection by `i`. Retains
 seed metadata as specified at input and through the actual connecting.Work.Support.B
 and grapheme.F.Tr.Location. No inventing smaller support mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Finset MeasureTheory
open Marker Lattice Wilson RG AllOrder AllOrder.Ink
open Push Push.AbsoluteSums Paths Animals
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open QuadraticLocal.Affinity
variable {V ι : Type} [DecidableEq V]{G:Gauge}{n c:Side}{P:Passport n V}{R:Census V}
variable {Y:V→Type}[∀ i, AddCommGroup (Y i)]{𝕜:Type}[RCLike 𝕜][NormedAlgebra 𝕜 ℂ][∀ i,Module 𝕜 (Y i)]
variable {A:∀ i,Set (Y i)}{K:∀ i,Submodule 𝕜 (Y i)}
local notation "Z"=> Wallet A
variable {X:ι→ Row P R G (Wallet A)}
-- audit before any instantiated Fold, Paint.Value representation
structure Tableau (K:∀ i,Submodule 𝕜 (Y i))(A:∀ i,Set (Y i))(X:ι→ Row P R G (Wallet A)) : Prop where
    bill i: Attn K A (X i).mode.val (X i).paint

namespace Tableau
variable (T:Tableau K A X)(C:Club X)(q:Ratio c n)
open Polish
include T
lemma line (B:BudgetPoint)(g:ℝ): Taut P.support A K (rendered X B g):=by
    refine ⟨fun i=> ?_, fun i V=> ?_⟩; exact (X i).heard _
    exact (T.bill i).sc ↑((X i).grain g V)
lemma alliance : Attn K A (Club.alliance X C).val (fun i=> ∏ j∈C.val,(X j).paint i):=by
    rw [Club.fulfills]; exact Polish.monomial C.val (fun i=> (X i).mode.val) _ (fun i _=> T.bill _) (Club.apart ..)
variable {j:ℕ} (S:Press X j) {a e:ℝ} (B:Press.Receipt X S a e) (ρ:ℝ) (W':BudgetPoint)
local notation "Q"=> (Press.placement X q S B ρ)
local notation "L"=> (Scene.letters X q S B ρ)
local notation "p₀"=> (P.coarser q)
lemma reply : Tableau K A (Press.placement X q S B ρ):=⟨fun i=> (T.alliance i.fst|>.cs ( (Press.plant X i.fst q S i.snd |>.atom.budget ρ :ℝ):ℂ))⟩
lemma grows : Tableau K A L:=by constructor; rintro (i|i); exact T.bill i.val; exact (T.reply q S B ρ).bill i
variable {Hp v:ℕ}(Vt: Width.Viewer X S a v)(g:ℝ)
lemma famous : Taut (p₀).support A K (Width.famous X q S B Vt W' Hp ρ g):= Tableau.line ( (show Tableau K A _ from (by exact ⟨fun i:Width.Inn X q S Vt Hp=> (T.reply q S B ρ).bill (Width.aisle X q S Vt Hp i) ⟩))) W' g -- syntax
lemma imagined : Taut (p₀).support A K (Width.imagined X q S B Vt W' Hp ρ g):= Tableau.line ( (show Tableau K A _ from (by exact ⟨fun i:Width.Shaded X q S Vt Hp=> (T.reply q S B ρ).bill i.val⟩))) W' g
lemma formal : Taut (p₀).support A K (Width.treasured X q S B W' ρ g):= Tableau.line (T.grows q S B ρ) W' g
end Tableau
-- later adapt on germs & couplings. 
end YM.QuadraticLocal.Earn
