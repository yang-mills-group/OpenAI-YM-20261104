import YM.XSpace.Compat.Petals
import YM.XSpace.Arch

/-!
# Bulk continuum approach in the infinite-space Fourier prescription
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sail
open YM.XSpace.Compat.KP
open Filter Set Metric Function Lattice Bloch Laurent Complex MeasureTheory Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable (A:List Axis)

def uncirc (p:E4):= bill tooth A p*(lamp p)⁻¹
def city (p:E4):= house p*uncirc A p
def glo (p:E4):= bill turned A p*water p
def maze (p:E4):=city A p-glo A p
abbrev penalty (A:List Axis): ℕ:= A.length-1
@[simp] lemma city_zero : city A 0=0:=by simp [city,uncirc]
lemma pave (A B: ℕ) : A-(B+1)≤A:=Nat.sub_le ..
lemma uncirc_paid : Tw (uncirc A) search (sizeL A-2):= (f_bill A).times inverse
lemma interior_pay : Tw (city A) search (sizeL A-2):= zero_add (sizeL A-2) ▸ (win_house (ι:=Unit)).times (uncirc_paid A)
lemma rim_cost (l:ℤ): Tw (city A) veranda l := (Weight.vanish _ _).stay fun _ p hp=> by rw [city,house_off p hp, zero_mul]
lemma moon : Tw (city A) whole (-2):=by apply pay_all (blend (interior_pay A) (rim_cost A (sizeL A-2)) stroll) (rim_cost A _) ?_; unfold sizeL; omega

lemma glo_rim (k:ℤ): Tw (glo A) veranda k:=by
  have hp : Tw (breeze 1) veranda (k-sizeL A+2) := (far_fee _ (le_refl 1) zero_lt_one zero_lt_one).use away_bounds
  have he:= ((g_bill (ι:=Unit) A).use (show veranda.look⊆ whole.look from fun x hx=>veranda.out hx)).times (hp.times ((reciprocal_high (ι:=Unit)).use (show veranda.look⊆ whole.look from fun x hx=>veranda.out hx)))
  rw [show sizeL A+(k-sizeL A+2+-2)=k by ring] at he; exact he
lemma maze_zero : Tw (maze []) search 0:=by
  let h:= diff_cut.times ((reciprocal_high (ι:=Unit)).use rake_subset)
  refine (((win_house (ι:=Unit)).times diff_inverse).sum h).stay ?_; intro _ p _; simp only [maze, city,uncirc,glo,bill,List.map_nil,List.prod_nil,one_mul, water]; ring
lemma maze_ticket : Tw (maze A) search (penalty A:ℤ):=by
  cases A with
  | nil=> exact maze_zero
  | cons i A =>
    let L:=i::A; let n:=penalty L; let h: Tw (fun p=> (bill tooth L p - bill turned L p)*city [] p) search (n:ℤ):=by
      have he:= (diff_bill (ι:=Unit) L).times (interior_pay [])
      rw [show sizeL L+1+(sizeL []-2)=n from by simp [L,n,sizeL,penalty]; omega] at he; exact he
    have ht := ((g_bill (ι:=Unit) L).use rake_subset).times maze_zero
    apply (h.sum (ht.soften (2*earth) (by positivity [earth_pos]) search_short (l:=(n:ℤ)) ?_)).stay _
    · simp [n,sizeL,L,penalty]
    intro _ p _; simp only [maze,city,uncirc,glo,bill,List.map_nil,List.prod_nil,one_mul]; unfold L; ring
lemma maze_whole : Tw (maze A) whole (penalty A:ℤ):= blend (maze_ticket A) ((rim_cost A _).diff (glo_rim A _)) stroll
lemma night : Tw (maze A) whole (-5):= pay_all (maze_whole A) ( (rim_cost A _).diff (glo_rim A _)) (by omega)
lemma mazes : Integrable (maze A) := asset_good (maze_whole A) (night A) ()
lemma wakes : Integrable (glo A) := (Matches.basic (n:=0) A).serves.delivered
lemma add_maze : city A=maze A+glo A:=funext fun i=> (sub_add_cancel (city A i) (glo A i)).symm
lemma expense_city : Integrable (city A):= add_maze A ▸ (mazes A).add (wakes A)

lemma order_pay : ∃ C:ℝ, 0<C ∧ ∀ x:E4,1≤‖x‖ → ‖retract (city A) x- ↑(ride A Maxwell.Green x)‖≤ C*(‖x‖^(3+A.length))⁻¹:=by
  let n:=penalty A; have hk : 3+A.length ≤ n+4:= by unfold n penalty; omega
  obtain ⟨C,hC,H⟩:= night_pay (maze_whole A) (night A); obtain ⟨D,hD,h⟩:= (Matches.basic (n:=n+4) A).rate
  let q:= ‖(↑tally:ℂ)‖*C+D; have hq : 0≤q:= by unfold q; positivity
  refine ⟨q+1,by positivity,fun x hx=>?_⟩; let r:=‖x‖; have hr : 0<‖x‖:= zero_lt_one.trans_le hx; have hp : x≠0:= norm_pos_iff.mp hr; rw [add_maze, retract, meal_sum (mazes A) (wakes A),mul_add,add_sub_assoc]; apply (norm_add_le ..).trans; rw [norm_mul]
  apply (add_le_add (mul_le_mul_of_nonneg_left (H () x hp) (norm_nonneg _)) (h x hx)).trans
  unfold q; rw [← mul_assoc,← add_mul]; change q*_ ≤ _; gcongr ?_*(‖x‖^?_)⁻¹
  all_goals first | positivity | linarith
lemma at_bound : ∃ C:ℝ,0<C∧∀ x:E4,1≤‖x‖ → ‖retract (city A) x‖ ≤ C*(‖x‖^(2+A.length))⁻¹:=by
  obtain ⟨C,hC,H⟩ := order_pay A; obtain ⟨D,hD,h⟩:= (skim_strength (ι:=Unit)).quotes A.length
  refine ⟨C+D+1,by positivity,fun x hx=>?_⟩; have hp: x ≠ 0:= norm_pos_iff.mp (zero_lt_one.trans_le hx); apply (norm_le_norm_sub_add _ (↑(ride A Maxwell.Green x))).trans
  have Hs : ‖(↑(ride A Maxwell.Green x):ℂ)‖≤ D*(‖x‖^(2+A.length))⁻¹:=by
    rw [← rides_skim (h:=Maxwell.freeSmooth hp)]; change ‖ride A skim x‖ ≤_; rw [reports A (skim_hd hp)]
    apply (ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ A.length skim x) (cyclists A)).trans
    simp_rw [cyclists_at,basis_norm,Finset.prod_const_one,mul_one]; convert! h () x hp using 1; rw [show (-2:ℤ) - A.length = -(↑(2+A.length):ℤ) by omega,zpow_neg,zpow_natCast]
  apply (add_le_add (H x hx) Hs).trans; rw [add_mul,add_mul,mul_comm 1]; have he : C*(‖x‖^(3+A.length))⁻¹ ≤ C*(‖x‖^(2+A.length))⁻¹:=by gcongr; omega
  linarith [show 0≤(‖x‖^(2+A.length))⁻¹ by positivity]
end YM.XSpace.Sail
