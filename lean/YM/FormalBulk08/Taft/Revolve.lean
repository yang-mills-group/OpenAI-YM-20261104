import YM.FormalBulk08.Taft.Kopan
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Taft
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Avenue Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{I:Type}{W:Lab G K I}{ρ:ChartRatio G}{E e r d D R n:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
lemma stall (F:Frame G d)(S T:Side): revise F (S*T)=revise F S * revise F T:= by
   rw [revise,revise,revise,Matrix.diagonal_mul_diagonal]; apply congr_arg; funext i; simp_rw [heightK_of_le _ (weightFits F i), PNat.mul_coe, Nat.cast_mul,mul_pow]
lemma start (F:Frame G d): revise F 1=1:= by unfold revise heightK Dawn.scale; ext i j; by_cases h:i=j<;>simp [Matrix.one_apply,Matrix.diagonal,h]
variable (F)
def transmission (Z:ℕ→ Pennants (Letter F)) (j:ℕ):ℕ→ Matrix (Letter F) (Letter F) ℝ
    | 0=>1
    | k+1=> noncontract F (Z j) * transmission Z (j+1) k

def bridge (K:KernelChoices)(W:Lab G K I)(a:hue G)(F:Frame G d)(ρ:ChartRatio G)(T:SectionData F)(hv:d+1≤D)(x:I)(N m:ℕ): Matrix (Letter F) (Letter F) ℝ:= revise F ((W.V x).S.steps m (N-m))* (transmission F (bornM (ρ:=ρ) (T:=T) (W:=W) a hv x N) m (N-m))⁻¹
lemma bridge_self (a:hue G)(F:Frame G d)(T:SectionData F)(h:d+1≤D)(x:I)(N:ℕ) : bridge K W a F ρ T h x N N=1:= by simp [bridge, transmission,Schedule.steps,start]
variable {F}
variable (q:Quota F H W o D E R)(h: LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)
lemma step_chain (S:Schedule)(m i:ℕ): S.steps m (i+1) =S.block m*S.steps (m+1) i:= by
   induction i with
   | zero=> simp [Schedule.steps]
   | succ i ih=> rw [Schedule.steps,ih]; rw [Schedule.steps, show m+(i+1)=m+1+i by omega,mul_assoc]
include q h a hs ht hb
lemma transmissible (N i:ℕ)(x:I)(hm:W.neck x ≤ i)(hp:i+n≤N): IsUnit (transmission F (bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x N) i n).det := by
    induction n generalizing i with
    | zero=>rw [transmission,Matrix.det_one];exact isUnit_one
    | succ k ih=>
       have hp': i<N:=by omega
       let U:= bornM (ρ:=ρ) (T:=T) (W:=W) a q.horizon x N
       have he:= nc_stamp (U i) _ ((mat_begins a h q hs ht hb x i N hm hp').1)
       rw [transmission,Matrix.det_mul]; exact ((tagBack he).1).mul (ih _ (by omega) (by omega)) -- nat explicit
omit h hs ht hb in
lemma contacted (N i:ℕ)(x:I)(hp:i<N) : bridge K W a F ρ T q.horizon x N i= wheel F (bridge K W a F ρ T q.horizon x N (i+1)) ((W.V x).S.block i) (bornM (ρ:=ρ) (T:=T) a q.horizon (W:=W) x N i):= by
    unfold bridge wheel; rw [show N-i=N-(i+1)+1 by omega,transmission, step_chain,stall,Matrix.mul_inv_rev] -- needs hp?<no>
    rw [←mul_assoc, mul_assoc _ _ ((transmission F (bornM (W:=W) (ρ:=ρ) (T:=T) a q.horizon x N) _ _)⁻¹)]
lemma laden (x:I)(i N:ℕ)(hp:W.neck x ≤ i)(hN:i≤N): Mob F (bridge K W a F ρ T q.horizon x N i):= by
    induction hN using Nat.decreasingInduction with
    | self=> rw [bridge_self]; exact empty_mob _
    | of_succ i hi ih=> rw [contacted q a _ _ _ hi]; exact overstep (ih (by omega)) (mat_begins a h q hs ht hb x i N hp hi).1
end YM.FormalBulk08.Taft
