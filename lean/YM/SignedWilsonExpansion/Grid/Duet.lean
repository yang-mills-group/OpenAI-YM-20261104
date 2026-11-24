import YM.SignedWilsonExpansion.Grid.Align
import YM.SignedWilsonExpansion.Pair
namespace YM.SignedWilsonExpansion.Overlap.Duet
/-! # Cohort of independent mark-mask words using the actual fields

Paired E12 and A (02), or equal: distinguish field label at P1 with lifetime instance parameters l,r. Mask = all for the connected pair. No mean-field term lost at this stage on
the independent model either. `Cabin` uses ``bill X q`` orientation. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open MS.Puff MS.Osc MS.Osc.Snap MS.Latch MS.Latch.Job MS.Rake.Geo MS.Rake MS.Rock MS.Rock.Path MS.Breeze MS.Vane
open FVA2 TreeView HighRank HighScale MarkRows MassShift MarkShift
open Align PhasePair
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{f F H H':Law G}
local notation "Φ" => (PlanetD G)
local notation "μ" => covMeasure Axis

local notation "B" => Press.portDeck G
variable {K: Land.Booked (Press.portDeck G)} (M:MS_Data G K)
local notation "J" => MarkRows.I (Press.portDeck G)

local notation "a" => Finset.univ (α:=Fin 2)
variable (x:Fin 2→QP)(hx:Injective x) (l r:Bool)
local notation "ζ" => fun (s:Bool)=> Energy.called (degreeX s) 2 G
local notation "L2" => fun (s:Bool)=> MarkRows.packet M (ζ s)
def extract (n:ℕ) : Reading G:= ∑ i:J,∑ j:J, (ζ l i:ℂ) • (ζ r j:ℂ) • pulse M x i j n
local notation "U" => Duet.extract M x l r
local notation "R0" => x 1-x 0
def freight (n:ℕ) (s:Clock ℝ): Law G:= queue M U n s+pack_source (R0) (L2 r) (L2 l) n s
def turnP (n:ℕ)(s:Clock ℝ):Law G:= cycle (Φ s.2) μ (U n s)+ freight M x l r n s
lemma walletQ (e:ℕ)(s:Clock ℝ): (L2 l) e s∈ Wallet G:= by beta_reduce; rw [MarkRows.own]; exact Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (stock M j e s)
lemma row_sim (e:ℕ)(s:Clock ℝ)(v:QP):
    pack_source v (L2 r) (L2 l) e s= ∑ i:J,∑ j:J,(ζ l i:ℂ) •(ζ r j:ℂ) • pack_source v (ear M (address j)) (ear M (address i)) e s:= by
    have h(t): ∀ u:ℕ, Cabin v (Φ s.2) μ (L2 r t s) ( L2 l u s )=∑ i:J,∑ j:J,(ζ l i:ℂ) •(ζ r j:ℂ) • Cabin v (Φ s.2) μ (ear M (address j) t s) (ear M (address i) u s):= by
       intro u; beta_reduce; have he (m:Bool) i n: (ζ m i:ℂ) • ear M (address i) n s∈Wallet G:= Submodule.smul_mem _ _ ( stock M i n s ); conv_lhs=> arg 5; rw [MarkRows.own]
       rw [mark_finR s.2 v _ (fun j _=> he l j _) ( walletQ M r t s) ]; refine Finset.sum_congr rfl fun i _=>?_ ; beta_reduce; rw [ MarkRows.own,mark_finL s.2 v _ (fun j _=> he r j _) ( he l i _ ) ]; exact Finset.sum_congr rfl fun j _=> (mark_quote v _ _).trans (smul_comm _ _ _)
    unfold pack_source; simp_rw [ h,Finset.smul_sum ]; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_comm )
include hx
lemma worthwhile (n:ℕ)(s:Clock ℝ): U n s ∈Wallet G:= by
    unfold Duet.extract; simp only [ Finset.sum_apply,Pi.smul_apply ]; exact Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (spool M x hx i j n s))
lemma open_clock (n:ℕ)(s:Clock ℝ): turnP M x l r n s =∑ i:J,∑ j:J,(ζ l i:ℂ) • (ζ r j:ℂ) • Vane.rhs (fun p (_:Unit)=> x p) (fun _=> planeF)
   ( constantP G Unit (Φ)) (constantP G Unit (Φ)) ( approach ( Tide.frameF Unit s.1 ) M ) ( Dial.spine M (roster i j) s.1 x ) a n () s.2:= by
     have he(e): U e s=∑ i:J,∑ j:J,(ζ l i:ℂ) •(ζ r j:ℂ) • pulse M x i j e s:= by unfold Duet.extract; simp only [ Finset.sum_apply,Pi.smul_apply ]
     let Cq(l:Law G):= cycle (Φ s.2) μ l
     let P:=deep G s.2; have hF: Cq (U n s)= P ( U n s ):=( Breeze.weightC ( worthwhile M x hx l r n s ) .. ).symm
     have hm i j:Cq (pulse M x i j n s)= P ( pulse M x i j n s ):= ( Breeze.weightC ( spool M x hx i j n s ) .. ).symm
     have center: queue M U n s=∑ i:J,∑ j:J,(ζ l i:ℂ) •(ζ r j:ℂ) • queue M (pulse M x i j) n s:= by
        unfold queue; simp_rw [ he, ←blvd,map_sum,map_smul,Finset.smul_sum ]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=>Finset.sum_comm)
     unfold turnP freight; unfold Cq at hm hF; rw [center,hF,row_sim]; simp_rw [he, map_sum, map_smul,planeF, weight_pulse M x hx, hm, smul_add,Finset.sum_add_distrib, add_assoc ]

lemma pace_X (n:ℕ)(s:Clock ℝ)(w:Legs (Lane4 G)) : HasDerivAt (fun t:ℝ=>U n (s.1,t) w) ( turnP M x l r n s w ) s.2:= by
    rw [ open_clock M x hx l r ]; unfold Duet.extract PhasePair.pulse; simp only [ Finset.sum_apply, Pi.smul_apply ]; refine HasDerivAt.fun_sum fun i hi=> HasDerivAt.fun_sum fun j hj=>?_ ; exact (( ( Vane.motion (builder M (tail_goal x hx s.1) (roster i j)) ( Dial.pin M (roster i j) s.1 hx ) Finset.univ_nonempty n ).pace () w (fun i=>Bool.noConfusion i) s.2 ).const_smul ( (ζ r j):ℂ ) ).const_smul (ζ l i:ℂ)
lemma provisionalX (n:ℕ)(w:Legs (Lane4 G))(t:ℝ): Tendsto (fun u:ℝ=> U n (t,u) w) atBot (𝓝 0) := by
    have he i j : Tendsto (fun u:ℝ=>pulse M x i j n (t,u) w) atBot (𝓝 0):= by
        let V:= Dial.spine M (roster i j) t x; obtain ⟨_,_,hW⟩:= (Dial.pin M _ _ hx).2.2 a (by simp) n
        unfold PhasePair.pulse; dsimp only; rw [ hW ]; unfold river; exact tendsto_integral_Iic_zero tendsto_id
    unfold Duet.extract; simp only [Finset.sum_apply,Pi.smul_apply]; have ht(i j:J) := (( he i j ).const_smul (ζ r j:ℂ)).const_smul (ζ l i:ℂ)
    simpa only [smul_zero, Finset.sum_const_zero] using ( tendsto_finsetSum Finset.univ (fun i _=> tendsto_finsetSum Finset.univ (fun j _=> ht i j) ) )
omit hx in
abbrev opposite (t:ℝ)(n:ℕ) := ∑ i:J,∑ j:J,(ζ l i:ℂ)*(ζ r j:ℂ)* Dial.book M (roster i j) t x a n
lemma opaIR (n:ℕ)(t:ℝ) : Tendsto (fun u:ℝ=> U n (t,u) [] ) atTop (𝓝 (opposite M x l r t n)):= by
    have he(i j:J): Tendsto (fun u:ℝ=>pulse M x i j n (t,u) []) atTop (𝓝 (Dial.book M (roster i j) t x a n)):= ( ( Dial.reports (roster i j) (tail_goal x hx t) ( Dial.pin M _ _ hx ) Finset.univ_nonempty n ).1 () )
    unfold Duet.extract opposite; simp only [ Finset.sum_apply,Pi.smul_apply,smul_eq_mul, mul_assoc ]; exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=> ( (he i j).const_mul _ ).const_mul _))
lemma tote (n:ℕ)(t:ℝ): ∃ k:ℕ,∀ s:ℝ,∀ w:Legs (Lane4 G), k<w.length → U n (t,s) w=0:= by
    have hp(i j:J): ∃ k:ℕ,∀ s w,k<List.length w→pulse M x i j n (t,s) w=0:= by obtain ⟨k,he⟩:= ( Vane.founded (builder M (tail_goal x hx t) (roster i j)) ( Dial.pin M _ t hx ) ( s:=a ) Finset.univ_nonempty n ).1; exact ⟨ k,fun s w hx=> he () s w (by omega)⟩
    choose k hk using hp; let V(i:J):= ∑ j:J,k i j;
    refine ⟨∑ i:J,V i,fun s w h=>?_ ⟩; unfold Duet.extract; simp only [Finset.sum_apply,Pi.smul_apply]; refine Finset.sum_eq_zero (fun i hi=> Finset.sum_eq_zero (fun j hj=>?_)); rw [ hk ]; simp; exact lt_of_le_of_lt ( le_trans (show k i j≤V i from by unfold V; exact Finset.single_le_sum (fun i _=> Nat.zero_le (k _ i)) hj ) (Finset.single_le_sum (fun i _=> Nat.zero_le (V i)) hi)) h
end
end YM.SignedWilsonExpansion.Overlap.Duet
