import YM.RG05Readout.Capture.Shelf
/-!
# Opening to new Census mid-step

Keep identical even unmasked units across T-Licensing. Doesn't assert
integrability outside the opening until dropped to usable slots. Computes
injection for charging one vacant slot a constant, without touching K.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge} {n:Side} {V:Type}[DecidableEq V] [Fintype V] {R B:Census V}{a b c e t y z:ℝ}
variable {X:Rep G n} {P:V→ Three G n}{o:V→ Site n}{w:V→ℝ}{F:Config G n→ Poly R}

lemma Alcove.opening (h:R.choices ⊆ B.choices) (ha:Alcove X P F o w t e c) :
    ∃ F':Config G n→Poly B, (∀ U,narrow h (F' U)=F U) ∧ Alcove X P F' o w t e c:=by
    obtain ⟨H,K,ψ,ν,hT,hS,hA,hB,hG,hp,hU,hΨ,hF⟩:= ha.chamber
    let K' i U:=wrap R B (K i U); let H' i U:= wrap R B (H i U)
    let f' U:= Mach B ν+∑ i,H' i U
    let Z:= play X B K' f'; let C:= (fun _:V=> (1:ℂ)); let h':= passable h
    have hx : ∀ U, (f' U).part B.quiet=0:=fun U=>by unfold f'; rw [Poly.part_plus,mute, Poly.part_sum,zero_add]; exact Finset.sum_eq_zero (fun i _=> (wrap_burn h (hA i)).sil U)
    have he i U:narrow h (H' i U)= H i U:= narrow_wrap h _; have hs : ∀ U,narrow h (f' U)= Mach R ν+∑ i,H i U:=by
       intro i; unfold f'; rw [map_add,map_sum]; simp_rw [he]; rw [narrow,feed_mach]
       simp only [one_mul,id_eq, Finset.sum_ite_eq',Finset.mem_univ,if_true]
    have hQ(U): narrow h (Z U)= F U:=by
       have hi:= congr_fun (carry_play h' C (R:=X) (K:=K') hx) U
       change narrow h (Z U)=play X R _ _ U at hi; unfold play at hi; change _= _ • (Poly.pass (narrow h (f' U))*field (fun i=>narrow h (K' i U)) _) at hi
       rw [hs] at hi; unfold K' at hi; simp_rw[narrow_wrap] at hi; rw [hi,hF]; rfl -- rfl not?
    refine ⟨Z,hQ,ha.clef,fun i=> ?_,fun i U=> ?_,ha.price,H',K',ψ,ν,wrap_towed h hT,wrap_towed h hS,fun i=> wrap_burn h (hA i),fun i=>wrap_flow h (hB i),hG,hp,fun i U=>?_,fun i j U=>?_,rfl⟩
    · exact (narrow_right h _ R.quiet).symm.trans (by rw [hQ];exact ha.value i)
    · exact (narrow_right h (Z U) (R.fire i)).symm.trans (by rw [hQ]; exact ha.tally ..)
    · exact (wrap_right h _ R.quiet).trans (hU i U)
    · change (wrap R B _).part (route h (R.fire i))+_= _; rw [wrap_right]; exact hΨ ..

def stuff (P: Three G n)(X:Rep G n)(y:ℂ): Three G n:= (fun U=> (P.1 U)+y*((X.eval U:ℝ):ℂ),fun U=> y+(P.2.1 U),P.snd.snd)
def spice (R:Census V)(v:V→ℂ)(Z: Config G n→Poly R) := fun U=> Poly.pass (Mach R v)*Z U
lemma spice_live (v:V→ℂ)(h:Integrable F (prior G n)): Integrable (spice R v F) (prior G n):=by
   let c:= Poly.pass (Mach R v); let L : Poly R→ₗ[ℂ] Poly R:={toFun:=(c*·),map_add':=fun a b=>mul_add ..,map_smul':=fun a b=>mul_smul_comm .. }
   exact (L.toContinuousLinearMap.restrictScalars ℝ).integrable_comp h
lemma spice_right (z:Three G n) : stuff z X 0=z:= Prod.ext (funext fun U=> by simp[stuff]) (Prod.ext (funext fun U=>by simp [stuff]) rfl)
lemma Alcove.spiced (ha:Alcove X P F o w t e c) (v:V→ℂ)(hc:∀ i,w i*‖v i‖ ≤ b)(hw:∀ i,0≤ w i):
    Alcove X (fun i=> stuff (P i) X (v i)) (spice R v F) o w t e (b+c):=by
    obtain ⟨H,K,ψ,ν,hT,hS,hA,hB,hG,hp,hU,hΨ,hF⟩:= ha.chamber
    let Z i U:= (P i).fst U + v i*(X.eval U:ℂ); have hk : (Mach R v).part R.quiet=0:=mute ..
    refine ⟨ha.clef,fun U=> ?_,fun i U=> ?_,fun i=> ?_,H,K,ψ,(fun i=> v i+ν i),hT,hS,hA,hB,hG, fun i=>?_,hU,hΨ,?_⟩
    · unfold spice; rw [Poly.quiet_mul, Poly.pass_part _ hk,one_mul,ha.value]
    · unfold spice stuff; rw [shock,Poly.pass_part _ hk,whisper _ _ hk,Accent.sing,one_mul]; rw [ha.value,ha.tally]
    · let p:=stuff (P i) X (v i); funext U; change ((X.eval U:ℝ):ℂ)*(v i + _)+_= Z i U; unfold Z; rw [← ha.price i,coin]; unfold stuff; dsimp only; ring
    · exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (hw i)).trans ((mul_add ..).trans_le (add_le_add (hc i) (hp i)))
    funext U; unfold spice; rw [hF,play,play]; let f' U := Mach R ν+∑ i,H i U
    have he : (Mach R (fun i=> v i+ ν i))= Mach R v+Mach R ν:=by unfold Mach; simp_rw [Extra.Trajectories.send_add,sum_add_distrib]
    rw [he,add_assoc,pass_add hk (show (f' U).part R.quiet=0 from (by unfold f'; rw [Poly.part_plus,mute,Poly.part_sum,zero_add]; exact sum_eq_zero fun j _=> (hA j).sil U)),mul_smul_comm,mul_assoc]
end YM.RG05Readout.Many
