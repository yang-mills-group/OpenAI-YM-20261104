import YM.OPE.Therm.Bath
/-!
# Pressures measured precisely with truncated local cut

Jobs use `take` of solutions at required face thresholds, independent of the
particular mesoscopic packing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Cradle
open Function Set Filter RG Lattice Wilson MeasureTheory Cells
open House (lease edges countables tape tape_env chilly meld fence sharing linn turnsHall press press_mono markSpaces hall)
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n:Side} {G:Gauge} {U V W : Config G n} {τ t C e:ℝ}
local notation "𝒞" => Config G n
local notation "η" => prior G n
variable (T:Tiling n)(R:Rep G n)(r:ℕ)(τ:ℝ)
local notation "Q"=>Stove.haloFee R r
local notation "Lx" => (Q+1)
local notation "W"=> Stove.energy R r -- remove conflict
local notation "V₀"=> (Fintype.card (Site n):ℝ)
local notation "d"=> Module.finrank ℝ G.Mat
local notation "N"=> T.side.val
def chute (i:T.Cell):= lease T i Lx
def cup (i:T.Cell)(U:𝒞):= -∑ x∈chute T R r i, Stove.energy R r x U
def gaugeW (i:T.Cell)(U:𝒞):= Real.exp (cup T R r i U)
def cell (i:T.Cell)(U:𝒞):= gaugeW T R r i U * tape (countables T i) τ U
def Z (i:T.Cell)(U:𝒞):= press (edges T i) (cell T R r τ i) U
def edgeLoss (C e:ℝ):= (House.vacant T Lx).card*C+ V₀*e

def touchW (r:ℝ)(J:ℕ):= (J:ℝ)*Module.finrank ℝ G.Mat*Real.log (4/r)
include R r
variable (hv:T.kind=.site)(h:Stove.Chart R r C e)
variable {R r}
include h
lemma cup_env (i:T.Cell) : Envelope (cup T R r i):= Envelope.neg (Envelope.sum (chute T R r i) (Stove.energy R r) (fun i=> ⟨h.bill i,C,h.paid i⟩))
lemma cup_bound (i:T.Cell)(U:𝒞) : ‖cup T R r i U‖ ≤ House.gx T Lx^4*C:=by
   unfold cup; rw [norm_neg]; apply ((norm_sum_le ..).trans (Finset.sum_le_sum (fun x hx=> h.paid x U))).trans_eq; rw [Finset.sum_const,nsmul_eq_mul,chute,House.lease_size]; push_cast; rfl
lemma cell_env (i:T.Cell) : Envelope (cell T R r τ i):= Envelope.mul (cup_env T h i|>.exp) (tape_env _)
omit h in
lemma cell_nonneg (i:T.Cell)(U:𝒞): 0≤cell T R r τ i U:=by unfold cell gaugeW tape;split<;> positivity
include hv
lemma cup_feet (i:T.Cell) : fence (edges T i) (cup T R r i):=by
   refine sharing (X:=House.links (T.chamber i)) ?_ (House.books T); apply House.local_fence.mpr; intro U V he; unfold cup; apply congr_arg Neg.neg; apply Finset.sum_congr rfl; intro j hj; exact (h.home j) _ _ (agrees_mono he (House.deed T i Q ((House.seated T hv (by omega)).1 (show j∈lease T i Lx from hj))))
lemma cell_feet (i:T.Cell) : fence (House.fullRoom T i) (cell T R r τ i):= fun U V he=> congr_arg₂ (·*·) (congr_arg Real.exp (sharing (cup_feet T hv h i) (House.holds T) U V he)) (House.cool_fence T i τ U V he)
lemma deposit (i:T.Cell) : fence (House.fullRoom T i) (Z T R r τ i):=by
   intro U V he; refine integral_congr_ae (Eventually.of_forall fun w=> cell_feet T τ hv h i _ _ ?_); intro v hv; unfold meld; split; rfl; exact he hv
lemma cell_turn (i:T.Cell)(U:𝒞) : cell T R r τ 0 (pull (T.omega i) (T.translateBy i) U)=cell T R r τ i U:=by
   let s:= T.omega i; let b:= T.translateBy i; let D(v):= chute T R r v; let V:= pull s b U; have he: cup T R r 0 V = cup T R r i U:=by
      unfold cup; unfold V; simp_rw [h.turn]
      have hp : D i= (D 0).image (affine s b):=by
         have hi:Injective (affine s b ):= (Push.Local.turnSites s b).injective
         ext x; obtain ⟨x,rfl⟩:= (show Surjective (affine s b) from (Push.Local.turnSites s b).surjective) x
         simp only [Finset.mem_image,hi.eq_iff,exists_eq_right]; exact (House.tour T hv i Lx (by omega)).symm
      change -(∑ x∈D 0, (W (affine s b x) U))= -(∑ x∈ D i, W x U) -- correct W affine
      rw [hp,Finset.sum_image (show Injective (affine s b) from (Push.Local.turnSites s b).injective).injOn]
   unfold cell gaugeW tape; rw [he]; simp_rw [House.cool_turn T hv i U]
lemma Z_turn (i:T.Cell)(U:𝒞) : Z T R r τ 0 (pull (T.omega i) (T.translateBy i) U)= Z T R r τ i U:=by
   rw [Z,House.press_turn (T.omega i) (T.translateBy i) (X:=edges T 0) (Y:=edges T i) (fun _ => House.ticket T hv i)]; unfold press; simp_rw [cell_turn T τ hv h i]; rfl
lemma surface (U:𝒞) : ‖R.exponent U- (R.scalar+∑ i,cup T R r i U)‖ ≤ edgeLoss T R r C e:=by
   let F x := W x U; let Y:Set (Site n):= ∅; let D(i):=chute T R r i; let X:=Finset.univ.biUnion D; let S:= House.vacant T Lx
   have ht:∑ i,cup T R r i U = -∑ x∈X,F x := by unfold cup; unfold X; rw [Finset.sum_neg_distrib,Finset.sum_biUnion]; intro i hi j hj he; exact House.soldApart T hv (by omega) he
   have hh: (∑ x∈X,F x)= (∑ x,F x)-(∑ x∈S,F x) := eq_sub_of_add_eq ((add_comm ..).trans (Finset.sum_sdiff (fun _ _=>Finset.mem_univ _)))
   have hU: ‖∑ x∈ S,F x‖ ≤ S.card*C:= ((norm_sum_le ..).trans (Finset.sum_le_sum (fun x (_:x ∈ S)=> h.paid x U))).trans_eq (by simp)
   rw [ht,hh,show R.exponent U-(R.scalar+-( (∑ x,F x)-(∑ x∈S,F x)))=(R.exponent U-R.scalar+(∑ x,F x))-(∑ x∈S,F x) by abel]; exact ((norm_sub_le ..).trans (add_le_add (h.rate U) hU)).trans_eq (add_comm ..)
omit hv in
lemma lowerZ {θ:ℝ} (hs:0<θ)(ht:4*θ ≤ τ) (he:θ≤1) (v:T.Cell) :
    Real.exp (-((House.gx T Lx)^4 * C) - touchW (G:=G) θ (edges T v).card) ≤ Z T R r τ v 1 :=by
   let U:𝒞 := 1; let A:= edges T v; let a:ℝ:=-((House.gx T Lx:ℝ)^4*C); let c:=Real.exp a
   have hh(W':𝒞)(hw: W' ∈ House.basins A θ U): c ≤ cell T R r τ v (meld A W' U):=by
       let X:= meld A W' U; have hx: X ∈ chilly (countables T v) τ:= fun i _=> by
           have ht' := House.mellow X U (t:=θ) (fun x=>?_ ) i
           · apply ht'.trans; simpa only [U,faceValue,square,travel,Step.pos_read,Step.neg_read, Pi.one_apply, inv_one,mul_one,Gauge.chord_one,add_zero] -- σ
           unfold X meld; split; rename_i h; exact hw _ h
           rw [mul_inv_cancel,G.chord_one]; exact hs.le
       unfold cell gaugeW tape; rw [if_pos hx,mul_one]; exact Real.exp_le_exp.mpr (abs_le.mp (cup_bound T h v _)).1
   change Real.exp (a - _) ≤ _; rw [sub_eq_add_neg,Real.exp_add]; apply le_trans (mul_le_mul_of_nonneg_left (House.lid (X:=A) U hs he) (Real.exp_pos _).le); rw [← integral_const_mul]; unfold Z press; refine integral_mono ((Envelope.mul (Envelope.const c) House.towel_env).integrable _) ((House.enclosed (cell_env T τ h v) (House.meld_meas measurable_id measurable_const)).integrable _) (fun i=>?_); by_cases hi:i∈ House.basins A θ U; · rw [show House.towel A θ U i = 1 from if_pos hi,mul_one]; exact hh i hi
   rw [show House.towel A θ U i= 0 from if_neg hi,mul_zero]; exact cell_nonneg ..
-- previous theorem use lower_Z. Build hub. avoid optimizing. Choose rival.
omit hv in
lemma central {θ :ℝ}(hs:0<θ)(ht:4*θ≤τ)(he:θ≤1): ∃ V:𝒞,
      (∀ U:𝒞,Z T R r τ 0 U ≤ 2* Z T R r τ 0 V) ∧ (Real.exp (-((House.gx T Lx)^4*C)-touchW (G:=G) θ (edges T 0).card) ≤ Z T R r τ 0 V):=by
   let J:= Z T R r τ 0; let b:=sSup (Set.range J); have hU:=lowerZ T τ h hs ht he 0; have hx : BddAbove (Set.range J):=by obtain ⟨C,H⟩:= (House.held_mass _ (cell_env T τ h (0:T.Cell))).cost; exact ⟨C,fun i ⟨x,hx⟩=> hx ▸ (le_abs_self _).trans (H x)⟩
   have hh(U:𝒞): J U ≤ b:= le_csSup hx ⟨_,rfl⟩; by_cases he : b ≤2*J 1; · exact ⟨1,fun U =>(hh U).trans he,hU⟩
   have ha:0< b:= (lt_of_lt_of_le (Real.exp_pos _) hU).trans_le (hh 1); obtain ⟨u,⟨U,rfl⟩,hp⟩:= exists_lt_of_lt_csSup (s:=Set.range J) (Set.range_nonempty J) (show b/2<b by linarith); refine ⟨U, fun V=> le_trans (hh V) ?_, hU.trans ?_⟩; · change b≤2* J U; linarith only [hp];
   change J 1 ≤ J U; linarith only [hp,lt_of_not_ge he]
end YM.OPE.Therm.Cradle
