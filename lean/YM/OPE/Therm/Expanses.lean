import YM.OPE.Therm.Mauve
/-!
# Room partition shell (unnormalized weight), explicit post-L energy prices

All argument readers are fixed before partition maximization. No integrity assumptions per
patch involving the selected state. The psi entropy rate pays stitching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Cradle
open Function Set Filter RG Lattice Wilson MeasureTheory Cells
open House (chilly countables press meld branch fresh fence aside warms spares edges tape)
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n : Side} {G:Gauge} {t C e:ℝ}
local notation "𝒞" => Config G n
local notation "E"=>Edge (Site n)
local notation "η" => prior G n
local notation "Ex" => Real.exp
section
variable {V: Type*}{X:V→Finset (Edge (Site n))} {w:Config G n→ℝ}{f:V→ Config G n→ℝ}{u: V→ℝ}
lemma spread (J:Finset V){S:Finset E}(Z:𝒞→ℝ) (H:House.stills S Z)(h:∀ i∈J, House.stills S (f i)): House.stills S (fun U=> (∏ i∈J,f i U)*Z U):=by
   intro U V hu; exact congr_arg₂ (·*·) (Finset.prod_congr rfl fun i hi=> h i hi U V hu) (H U V hu)
lemma monied (J:Finset V)(f:V→𝒞→ℝ)(Z:𝒞→ℝ)(hz:Envelope Z)(h:∀ i∈J,Envelope (f i)): Envelope (fun U=> (∏ i∈J,f i U)*Z U):= (branch J _ h).mul hz
open scoped Classical in
lemma tunnels (J:Finset V)(he:Envelope w)(hw:∀ i∈J, House.stills (X i) w)(hf:∀ i∈J, Envelope (f i))(hu:∀ i∈J,∀ V, press (X i) (f i) V=u i)(hh:∀ i∈J,∀ j∈J,i≠j → House.stills (X i) (f j)) :
    (∫ U,(∏ i∈J,f i U)*w U∂η) = (∏ i∈J,u i)*∫ U,w U∂η:= by
   induction J using Finset.induction_on with
   | empty=> simp
   | insert i J hi ih =>
     let W(U):=(∏ i∈J,f i U)*w U; simp only [Finset.forall_mem_insert] at hw hf hu hh
     have ht := spread (f:=f) J w hw.1 (fun j hj=> hh.1.2 j hj fun H=> hi (H ▸ hj)); have hX :(∫ U,W U∂η)= (∏ i∈J,u i)*∫ U,w U∂η:= ih hw.2 hf.2 hu.2 (fun i hi'=> (hh.2 i hi').2)
     simp_rw [Finset.prod_insert hi,mul_assoc]; change (∫ U,(f i U)*W U∂η)=_
     rw [← fresh (X i) (hf.1.mul (monied J f w he hf.2))]; simp_rw [House.pressmul (X:=X i) (h:=ht),hu.1]; rw [integral_const_mul,hX] -- fix
lemma towards (J:Finset V)(he:Envelope w)(hW:∀ U,0≤w U)(hw:∀ i∈J,House.stills (X i) w)(hf:∀ i∈J,Envelope (f i))(hz:∀ i∈J,∀ U,0≤ f i U)(hu:∀ i∈J,∀ V, press (X i) (f i) V≤u i)(hh:∀ i∈J,∀ j∈J,i≠j → House.stills (X i) (f j)) :
    (∫ U,(∏ i∈J,f i U)*w U∂η) ≤ (∏ i∈J,u i)*∫ U,w U∂η:= by
   induction J using Finset.induction_on with
   | empty=> simp
   | insert i J hi ih =>
     let W(U):=(∏ i∈J,f i U)*w U; simp only [Finset.forall_mem_insert] at hw hf hu hh hz
     have ht := spread (f:=f) J w hw.1 (fun j hj=> hh.1.2 j hj fun H=> hi (H ▸ hj)); have hX :(∫ U,W U∂η)≤ (∏ i∈J,u i)*∫ U,w U∂η:= ih hw.2 hf.2 hz.2 hu.2 (fun i hi'=> (hh.2 i hi').2)
     have hV:= monied J f w he hf.2; have hU : 0 ≤ u i:= le_trans (show 0≤ press (X i) (f i) 1 from integral_nonneg fun _=> hz.1 _) (hu.1 1); simp_rw [Finset.prod_insert hi,mul_assoc]; change (∫ U,(f i U)*W U∂η)≤_
     rw [← fresh (X i) (hf.1.mul hV)]; simp_rw [House.pressmul (X:=X i) (h:=ht)]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hX hU); rw [← integral_const_mul]; exact integral_mono (((House.held_mass _ hf.1).mul hV).integrable _) ((hV.integrable (η)).const_mul _) fun U=> mul_le_mul_of_nonneg_right (hu.1 _) (mul_nonneg (Finset.prod_nonneg fun j hj=> hz.2 j hj U) (hW U))
end
variable (T:Tiling n)(R:Rep G n)(r:ℕ)(τ:ℝ)
variable {R r}
variable (hv:T.kind=.site)(h:Stove.Chart R r C e)
local notation "M"=> T.side.val
local notation "ν" => Fintype.card T.Cell
local notation "T$"=> touchW (G:=G)
include hv h
-- read all rooms separately from common seam. Interiors touching outside not read
lemma expanse (hy: 0 < t)(ht:t≤1)(hP:4*t+τ ≤ R.p.threshold)(hb:2 ≤ M) {σ K Λ δ w:ℝ} (H:R.Lawful σ K Λ δ w) (hz:∀ U,0≤R.eval U) (V:𝒞) :
    Ex (R.scalar-edgeLoss T R r C e - T$ t (House.seam T).card) * (Z T R r τ 0 V)^ν ≤ ∫ U : 𝒞,R.eval U∂η:= by
   let X:= House.seam T; let Y:= House.fromZig T V; let s U:= House.towel X t Y U; let F U := meld X Y U; let W i:= cell T R r τ i; let A i u:= W i (F u); let z:= Z T R r τ 0 V; let d:= Ex (R.scalar-edgeLoss T R r C e)
   have hel i : ∀ U, press (edges T i) (A i) U=z:=by
     intro U; have he : press (edges T i) (A i) U= press (edges T i) (W i) Y:=by
        refine integral_congr_ae (Eventually.of_forall fun u=>?_); change W i _= W i _; apply cell_feet T τ hv h; intro x hx
        rcases Finset.mem_union.mp (House.sails T hv i hx) with ht|ht
        · unfold F X; simp only [meld,if_pos ht, if_neg (Finset.disjoint_left.mp (House.sealing T i) ht)]
        unfold F X; simp only [meld,if_pos ht,if_neg (Finset.disjoint_right.mp (House.sealing T i) ht)]
     rw [he]; change Z T R r τ i Y=_; rw [← Z_turn T τ hv h]; exact deposit T τ hv h 0 _ _ (House.fence_iff.mp (House.presents T hv (hn:=hb) i V))
   have hf (i): Envelope (A i):= House.enclosed (cell_env T τ h i) (House.meld_meas measurable_const measurable_id)
   have hw:=House.towel_env (X:=X) (t:=t) (U:=Y)
   have heA i: fence (edges T i) (A i):= fun U V he => cell_feet T τ hv h i (F U) (F V) (fun x hx =>by
      unfold F meld; split; rfl; rename_i ht; exact he (show x∈edges T i from (Finset.mem_union.mp (House.sails T hv i hx)).resolve_left ht))
   have hh : (∫ U,(∏ i,A i U)*s U∂η)= z^ν * ∫ U,s U∂η:=
      (tunnels Finset.univ hw (fun i _=> spares House.towel_fence (House.sealing T i)) (fun i _=> hf i) (fun i _=> hel i) (fun i _ j _ h=> spares (heA j) (aside T hv h|>.symm))).trans (by simp [s])
   have hl : (∫ U,d*((∏ i,A i U)*s U)∂η) ≤ ∫ U,R.eval U∂η:=by
      refine integral_mono (((monied Finset.univ A s hw (fun i _=>hf i)).integrable η).const_mul _) ((R.envelope H).integrable _) ?_
      intro U; dsimp only; by_cases hs:U∈House.basins X t Y; swap; · rw [show s U=0 from if_neg hs,mul_zero,mul_zero]; exact hz U
      rw [show s U=1 from if_pos hs,mul_one]; by_cases ha: ∀ i,F U∈chilly (countables T i) τ; swap
      · push Not at ha; obtain ⟨i,hi⟩:=ha; rw [Finset.prod_eq_zero (i:=i) (Finset.mem_univ _) (by dsimp only [A,W,cell,tape]; rw [if_neg hi,mul_zero]),mul_zero]; exact hz U
      have ht i : A i U=Ex (cup T R r i U):=by
         unfold A W cell tape; rw [if_pos (ha _),mul_one]; exact congr_arg Ex ((cup_feet T hv h i) _ _ ((House.meld_off X Y U).mono (fun x hx=> Finset.mem_compl.mpr (Finset.disjoint_right.mp (House.sealing T i) hx))))
      simp_rw [ht]; rw [← Real.exp_sum, show d= Ex _ from rfl, ← Real.exp_add,Rep.eval,Activities.gas_one _ _ (House.cleanEnough T hs hy.le _ hP ha),mul_one]; exact Real.exp_monotone (by linarith only [(abs_le.mp (surface T hv h U)).1])
   rw [integral_const_mul,hh] at hl; apply le_trans ?_ hl; rw [sub_eq_add_neg (R.scalar-_),Real.exp_add]; have hZ :0≤z:= integral_nonneg fun _=> cell_nonneg ..
   apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (House.lid Y hy ht) (Real.exp_pos _).le) (pow_nonneg hZ _)).trans_eq; dsimp only [s,touchW]; unfold d X; ring
end YM.OPE.Therm.Cradle
