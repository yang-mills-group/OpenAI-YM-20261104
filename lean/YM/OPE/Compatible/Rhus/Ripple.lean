import YM.OPE.Compatible.Rhus.Cradle
/-! Mix Sleep alphabet and ideal bridge to EOM hierarchy -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp Source Drops WardBin Planned.PrimaryIntegral295.Parts
open scoped Topology BigOperators Classical
variable {r d m n j:ℕ}{c:ℝ}{W:Type*}{G:Gauge}
namespace Script
open Page
abbrev rollReading (A: MixX G r n d)(x:Snap G d):ℂ:= ((A.1.val (fun _=>x)):ℂ) + Complex.I * ((A.2.val (fun _=>x)):ℂ)
abbrev Spired (G:Gauge) (r n j:ℕ) := (↥(Grade (G:=G) (d:=j) (n+r,r)))
abbrev Reading (P: Spired G r n j)(A:MixX G r n d):Prop:= ∀ x:Jet G,Labels.read x P.val.val=rollReading A (trunk d x)
lemma surge_mix (p:Spired G r n j) (h:j≤d):∃ A:MixX G r n d, Reading p A:=by
    obtain ⟨B,hB,ht⟩:=surged p.val p.property d; have hx:= surgedFields p.val d hB ht; have hh:=germKitchen p.val d hB ht p.property
    have hu (f:ℂ →ₗ[ℝ]ℝ) : ∃ Q:partX G r n (d-1),∀ x:Fin r→Snap G d,Q.val x=f (B x):=by
       let Y: Chord G (d-1) r:= f.compMultilinearMap B.toMultilinearMap; have hQ : Y ∈ partX G r n (d-1):=by
          refine Off.mk (fun x α=> congr_arg f (ht x α)) (fun g x=> congr_arg f (hx g x)) (fun i t ha=> ?_); change f (B _) = 0; rw [hh i t ha,map_zero]
       exact ⟨⟨Y,hQ⟩,fun _=>rfl⟩
    obtain ⟨Q,hQ⟩:=hu Complex.reLm; obtain ⟨R,hR⟩:=hu Complex.imLm
    refine ⟨(Q,R),fun t=>?_⟩; rw [← returnL h t,← hB]; change Tensor.diagonal B _= (↑(Q.val _):ℂ) + Complex.I*↑(R.val _); rw [hQ,hR,mul_comm Complex.I]; exact (Complex.re_add_im _).symm
lemma mixUni (Q R:MixX G r n d) (h:∀ v, rollReading Q v=rollReading R v): Q=R:=by
   obtain ⟨A,hA,-,-,ha⟩:=coloredLift Q; obtain ⟨B,hB,-,-,hb⟩:=coloredLift R
   have ht: A=B:= Tensor.ext_diag A B ha hb (funext (fun x=>(hA _).trans ((h x).trans (hB _).symm)))
   have hu(x:Fin r→ Alphabet G (d-1)): Q.1.val x=R.1.val x ∧ Q.2.val x=R.2.val x:=by
      rw [← ht] at hB; have hh:= (hA x).symm.trans (hB x)
      constructor
      · simpa using congr_arg Complex.re hh
      simpa using congr_arg Complex.im hh
   exact Prod.ext (Subtype.ext (MultilinearMap.ext fun x=> (hu x).1)) (Subtype.ext (MultilinearMap.ext fun x=> (hu x).2))
lemma tiled (h:n+r≤j)(t:MixX G r n d) : ∃ p:Spired G r n j, Reading p t:=by
   obtain ⟨p,hp,hv⟩:= liftedTile t h; exact ⟨⟨p,hp⟩,hv⟩
def readWall (d:ℕ)(hj:j≤d)(p:Spired G r n j): MixX G r n d:= (surge_mix p hj).choose
lemma Read_reads (d:ℕ)(hj:j≤d)(p:Spired G r n j) : Reading p (readWall d hj p):=(surge_mix p hj).choose_spec
lemma rollAdd (p q:MixX G r n d) (x:Snap G d): rollReading (p+q) x=rollReading p x+rollReading q x:=by
   rcases p with ⟨A,B⟩;rcases q with ⟨Q,R⟩; change (((A.val (fun _=>x)+ Q.val (fun _=>x)):ℝ):ℂ)+Complex.I*((((B.val (fun _=>x)+R.val (fun _=>x)):ℝ):ℂ))=_; unfold rollReading; push_cast; ring
lemma rollScale (p:MixX G r n d)(t:ℝ)(x:Snap G d):rollReading (t • p) x=t • rollReading p x:=by
   unfold rollReading; simp only [Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul_of_tower,smul_apply]; simp [Complex.real_smul]; ring
end Script
end YM.OPE.Flume
