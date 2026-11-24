import YM.RG05Readout.Pulse.Openly
import YM.RG05Readout.Nuclear.Hermite
/-! Real support pairing supplied. Target uses profile ν_t with derivatives at least
 sum of dimensions + 4p. Use `Tall` as pointwise C norms through t as in text;
 Sobolev norms versions would need corresponding embedding. No Hölder charges.
 Room.Profile supports support exact location.K.Tile.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Pulse
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k D:ℕ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "X!"=> C.side N p
local notation "Y!"=> C.side b p
local notation "G!"=>C.S.gridPoint
local notation "o!"=> C.S.place
local notation "ρ₀"=>C.S.radius p
local notation "W!"=> Wave V
local notation "X0"=> Cloud V
variable (s:V→ℕ) (h:b ≤ N)(o: V→ Site (C.side b p)) (q η:ℝ) (f: Wave V)
/-- Scattering test.Cell physical regions. No axis Screen. -/
def Scattering (f:Wave V) (η:ℝ):= ∀ x∈tsupport f.val, ∀ i j:V,i≠j → η ≤ ‖x i-x j‖
abbrev buy (C:Family G)(b p:ℕ)(o:V→Site (C.side b p))(η:ℝ): Nuclear.Allow V:= fun f=>Halls.carton C b (lift ∘ o) f η
local notation "u"=> cropX f o q
local notation "r"=> Λ h p
local notation "T"=> Site (r).count
local notation "K"=>buy C b p o
omit [DecidableEq V] in
lemma territory (h: Scattering f η)(hr: 0 < q)(a t:ℝ)(hp: t+2*A b*a ≤ q*η):
   Plant Native.box (K t) u a:=by
    intro τ _ x hx F ht i j he v hv w hw
    let d: X0:= fun i=> q⁻¹ • (o! (o i)-A b • τ); let z:= fun i:X0=> d+(q⁻¹*A b) • i; have hQ: (u τ).val= f.val ∘ z:=rfl
    have hh: z x ∈ tsupport f.val:=by rw [hQ] at hx; refine closure_minimal ?_ (IsClosed.preimage (f:=z) (continuous_const.add (continuous_id.const_smul (q⁻¹*A b)) : Continuous z) (isClosed_tsupport f.val)) hx; exact fun i hi=> subset_closure (show z i ∈ support _ from hi)
    let X(i:V)(v):=o! (o i)+ A b • v; have hv' := h _ hh _ _ he
    have hp': z x i-z x j=q⁻¹ • (X i (x i)-X j (x j)):=by
       have hk(i): z x i=q⁻¹ • (X i (x i)- A b • τ):=by
           unfold X; change q⁻¹ • _+(q⁻¹*A b) • x i=_;rw [mul_smul,← smul_add];congr 1; abel
       rw [hk,hk,← smul_sub,sub_sub_sub_cancel_right]
    rw [hp',norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le] at hv'; have ht': η*q ≤ ‖X i (x i)-X j (x j)‖ :=by rw [mul_comm q⁻¹,← div_eq_mul_inv] at hv'; exact (le_div_iff₀ hr).mp hv'
    have hz (i:V)(x y:E4)(h:‖x-y‖ ≤ a) : ‖X i x-X i y‖≤ A b*a:=by
        unfold X; rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg (C.S.a_pos _).le]; exact mul_le_mul_of_nonneg_left h (C.S.a_pos _).le
    let V':=X i v; let W:= X j w; let g:= X i (x i); let g':= X j (x j); change t ≤ ‖V'-W‖
    linarith only [norm_sub_le_norm_sub_add_norm_sub g V' W,norm_sub_le_norm_sub_add_norm_sub g W g',hz i (x i) v (by rw [norm_sub_rev]; exact ht _ _ hv.2),hz j w (x j) (ht _ _ hw.2), hp, show η*q≤ ‖g-g'‖ from ht'] -- norm triangle
omit [DecidableEq V] in
lemma crop_cont : Stone d Native.box u:=by
   intro i _ x; unfold cropX; simp_rw [shoots]; let y(τ:E4)(i:V):=q⁻¹ • (C.S.place (o i)- C.S.a b • τ); have hy:Continuous y:= continuous_pi (fun i=> by fun_prop); exact (Continuous.continuousOn (show Continuous (fun τ=> ((q⁻¹*A b)^i) • iteratedFDeriv ℝ i f.val (y τ+(q⁻¹*A b) • x)) from ((lit f i|>.continuous_iteratedFDeriv (m:=i) le_rfl).comp (hy.add continuous_const)).const_smul ((q⁻¹*A b)^i)))
omit [DecidableEq V] in
lemma inflame (hr: 0 <q)(hp:q ≤ A b) {μ:ℝ}(hd:Tall f d 1 μ)(x:E4) : Tall (u x) d 1 ((A b/q)^d*μ):=by
   intro i h y; unfold cropX; rw [shoots,norm_smul, one_pow,one_mul, mul_comm q⁻¹,← div_eq_mul_inv,Real.norm_of_nonneg (pow_nonneg (div_nonneg (C.S.a_pos _).le hr.le) _)]
   let z:=((fun i=> q⁻¹ • (C.S.place (o i)- C.S.a b • x))+ (A b/q) • y); exact mul_le_mul (pow_le_pow_right₀ ((one_le_div hr).mpr hp) h) (show ‖iteratedFDeriv ℝ i f.val z‖ ≤ μ from (hd _ h z).trans_eq (by simp)) (norm_nonneg _) (pow_nonneg (div_nonneg (C.S.a_pos _).le hr.le) _)
-- cost.Norm independent of t for OPE demand: query d ONLY related to profile norm, not pert iteration
noncomputable def gustCost (C:Family G)(b:ℕ) (η q:ℝ):= η/16 * q/C.S.a b
noncomputable def earn (s:V→ℕ)(C:Family G)(b d:ℕ)(η q:ℝ):ℝ:= let z:=gustCost C b η q; (mintBase s 2 d * z⁻¹^((∑ i:V,(s i+2))+4*Fintype.card V)+(redeem s d 2*2+1)*z)*(C.S.a b/q)^(d+1) -- A uses shadow
lemma regent (hr:0<q)(he: q ≤ A b) (hη:0 < η) (hp: η ≤1) (hs:(∑ i:V,(s i+2))+4*Fintype.card V < d+1) (hΨ:Scattering f η){x:ℝ}(hx:0 ≤x)(hX:Tall f (d+1) 1 x):
   let a:=fun w:V→T=> placeR (r) ∘ w
   ∃ G', Bouquet s Native.box (K (q*η/2)) G' (earn s C b d η q*x) ∧ ∀ (τ:E4) k, k ≤ ∑ i,s i→ ∀ w: V→T,pie (G' τ) (u τ) k (a w):=by
     intro a; let z:=gustCost C b η q; have H:0<z:= div_pos (mul_pos (by positivity) hr) (C.S.a_pos _)
     have hT: z ≤ 1:=by unfold z gustCost; rw [div_le_one (C.S.a_pos _)]; exact le_trans (mul_le_of_le_one_left hr.le (by linarith)) he
     have hP:q*η/2 + 2*A b*(2*z) ≤ q*η:=by unfold z gustCost; have hx:= C.S.a_pos b; field_simp; norm_num;try linarith
     let L:= Finset.univ.image a; have ht(i)(hh:i∈L): ‖i‖ < (2:ℝ):=by
        obtain ⟨w,hi,rfl⟩:= Finset.mem_image.mp hh; calc
          ‖a w‖ ≤ 1:= (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i=>Pert.Cellular.cells_bd (show a w i∈Native.box by change (placeR (r) (w i))∈ Native.box; simpa only [smul_zero, add_zero] using mapsR (r) (C.S.toDepth_odd _ _) (w i) Native.box0))
          _ < _:=one_lt_two
     obtain ⟨G',hG,H'⟩:= vitality s Native.box (K (q*η/2)) u 2 z L (crop_cont o q f) (territory o q η f hΨ hr _ _ hP) (fun i _=> inflame o q f hr he hX i) (show 0 ≤ (A b/q)^(d+1)*x from mul_nonneg (pow_nonneg (div_nonneg (C.S.a_pos _).le hr.le) _) hx) le_rfl H hT hs zero_le_two ht
     refine ⟨G',hG.permit (fun _ _=> rfl) (le_of_eq ?_), fun τ i hx w=> H' τ _ (Finset.mem_image_of_mem _ (Finset.mem_univ w)) i (let H:=le_trans hx (Finset.sum_le_sum (g:=fun i:V=> s i+2) (s:=Finset.univ) (fun i _=>Nat.le_add_right ..)); by omega)⟩; unfold earn z; dsimp only;ring
end YM.RG05Readout.Pulse
