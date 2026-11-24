import YM.FVAAlt2.GhostDet
import YM.FVAAlt2.Unroll

/-! Embedding Bose sector into `S` and occupancy of the ghost derivative.
Occupancy proof also needed for shifts of the coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Bos
open Finset Function MS MS.Koszul MS.Book MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Swirl MS.Cylinder MS.Puff MS.Plane
open Pert.Orb Lattice Topology SchemeRG11.Sway PertExtension GaussianScore
open scoped PowerSeries
variable {G:Gauge}{n:Side}{ι κ:Type} [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
local notation "p" => isOdd (ι:=ι) (κ:=κ)
local notation "𝑷" => PowerSeries (Com p)
local notation "𝑩" => PowerSeries (Bos ι)
local notation "S"=> Alpha ι κ
local notation "Γ"=> landLaw G n
local notation "f!" => Com.forget (pNo ι)
set_option linter.unusedSectionVars false

def projVec (ι κ:Type)[DecidableEq ι][DecidableEq κ] : Matrix (Alpha ι κ) ι ℂ:= fun y i=> if y=avec i then 1 else 0 -- DecEq κ needed!
lemma tiePV : Tie (pNo ι) p (projVec ι κ):=by intro i j h; by_cases he: j=avec i; rw [he]; rfl; exact (h (if_neg he)).elim

def up : Bos ι→ₐ[ℂ] Com p:= Com.transform tiePV
@[simp] lemma up_v(x:Bos ι): (up (κ:=κ) x).val=pull (projVec ι κ) x.val:= rfl
abbrev upS : PowerSeries (Bos ι)→+* PowerSeries (Com p):= PowerSeries.map up.toRingHom

lemma fade (x:Bos ι)(i:κ): Glue.Stops i (up x):= by unfold Glue.Stops; rw [up_v,pull_D]; simp [projVec,antigh,avec]
lemma Silence (x:𝑩)(i:κ): Glue.Silent i (upS x):= by intro j; rw [upS,PowerSeries.coeff_map]; exact fade _ _
lemma wire_up (x:𝑩): Com.forget p (upS x)=pullSeries (projVec ι κ) (f! x):= by
 funext i; rw [Com.forget_at,upS,PowerSeries.coeff_map]; rfl

lemma scale_up(z:ℂ)(x:𝑩): upS (κ:=κ) (z • x)=z • upS x:=by ext1 i; change PowerSeries.coeff i _= PowerSeries.coeff i _; unfold upS; simp_rw [PowerSeries.coeff_smul,PowerSeries.coeff_map,PowerSeries.coeff_smul]; exact map_smul up z _

lemma launch {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
    (z:ι→X)(U:X→ℝ)(h:Taylor.germ U):
    pull (projVec ι κ) (Taylor.ink z U)=Taylor.ink (Sum.elim z (fun _:κ⊕κ=>0) : Alpha ι κ→X) U:= by
 let L(i:Alpha ι κ)(j:ι):ℝ:= if i=avec j then 1 else 0
 let Y:Alpha ι κ→X:=Sum.elim z fun _=>0
 have he(i): Y i=∑ j,L i j • z j:= by rcases i with k|k <;> simp [Y,L,avec,ite_smul]
 have hz: projVec ι κ=(fun i j=> Complex.ofReal (L i j)):=Matrix.ext fun i j=>by simp [projVec,L,apply_ite]
 rw [hz,Taylor.scale_pos z Y L he h]; exact Eq.symm (eq_pull _ (region.symm _))

variable (A:Module.Basis ι ℝ (Land G n))
local notation "v"=> propagator (κ:=κ) A
-- wick on pure even
abbrev white (A:Module.Basis ι ℝ (Land G n)) : Matrix ι ι ℂ:=fun i j=> (1/2:ℂ) * (landLaw G n).wick (A.coord i) (A.coord j)
lemma chill_eq : pullCov v (projVec ι κ) = white A:= by ext i j; unfold pullCov propagator; simp_rw [Matrix.mul_apply, Matrix.transpose_apply,Matrix.smul_apply,Fintype.sum_sum_type, projVec]; simp [avec, Rcov,white]
lemma view_up (x:Bos ι): View v (up x).val= View (white A) x.val:= by rw [up_v,pull_View _ _ x.small,chill_eq]
lemma wick_up (x:𝑩): Glue.wick A (upS (κ:=κ) x)= ℶV (white A) (f! x):=by funext i; rw [Glue.wick_at,upS,PowerSeries.coeff_map]; exact view_up A _
end YM.FVAAlt2.Bos
