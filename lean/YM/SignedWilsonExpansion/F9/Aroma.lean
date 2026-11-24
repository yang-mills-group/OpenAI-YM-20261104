import YM.SignedWilsonExpansion.F9.Commit
/-!
# Signed calls, filtration-preserving all-orders formal family

Before commissioning estimator has mesh scales; preserve strict rank and weight support.
-/
set_option autoImplicit false
set_option maxHeartbeats 385000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace Stair
open Cirrus
open Normalize (Sec Formal)
open Tape
variable (W:Initialize G){A'' :∀ h,Rays G h W.hol}{Ω:Council F}{P':Normalize.Store G}
variable (q': Stair Ω (launch F W.hol W.surveys A'' k) A Ñ m c c h e k u Z)
section prime
abbrev Folia (G:Gauge)(d h:ℕ): Submodule ℂ (Sec G h):= (Maxwell.shellSector G d).comap (Normalize.coeS h)
def Trustee (L: Label G h→ₗ[ℂ]Sec G h) (z:ℂ): Prop:= L (Labels.unit G h)= z • Normalize.leaf G h ∧
    (∀ d≤h,∀ x:Label G h,x.val∈localFields G d→ L x∈ Folia G d h) ∧
    (∀ x,L (realBar x)=Normalize.reel h (L x))∧ (∀ s:Signed,∀ x,L (tensor s.ortho x)=Normalize.ori s.ortho h (L x))
lemma trustee_board (F:Labels.Frame G h)(L: Label G h→ₗ[ℂ]Sec G h){u:ℂ}(hu:L (F.basis 0)=u • Normalize.leaf G h) (H:∀ d≤h,∀ x:Label G h,x.val∈ localFields G d→ L x∈Folia G d h)
    (p:∀ i,Normalize.reel h (L (F.basis i))=L (F.basis i))(v:∀ s:Signed,∀ i:F.Index, Normalize.ori s.ortho h (L (F.basis i))=∑ j, (↑(realM F s j i):ℂ) • L (F.basis j)) : Trustee L u:=by
    refine ⟨ F.starts_unit ▸ hu,H, fun x=>?_,fun s x=>?_⟩
    · rw [← F.basis.sum_repr x]; simp only [map_sum, realBar.map_smulₛₗ,(Normalize.reel h).map_smulₛₗ,map_smul,F.realForm,p]
    rw [← F.basis.sum_repr x]; simp_rw [map_sum,map_smul]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [v]; apply congr_arg (_ • ·); nth_rw 1 [← F.basis.sum_repr (tensor s.ortho (F.basis i))]; rw [map_sum]; refine Finset.sum_congr rfl fun j _=> ?_; rw [map_smul]; change F.coords (tensor s.ortho (F.basis i)) j • _= _; rw [← F.act_coords,F.coords_basis, bleach_even]
lemma galleryH (F:Frames G) {L: Label G h→ₗ[ℂ] Sec G h}{u:ℂ}(hu:L (Labels.unit G h)=u • Normalize.leaf G h) (H:∀ i:(F.level h).Index,L ((F.level h).basis i)∈ Folia G (wt (F.level h) i) h)
    (p:∀ i,Normalize.reel h (L ((F.level h).basis i))=L ((F.level h).basis i))(v:∀ s:Signed,∀ i:(F.level h).Index, Normalize.ori s.ortho h (L ((F.level h).basis i))=∑ j, (↑(realM (F.level h) s j i):ℂ) • L ((F.level h).basis j)): Trustee L u:=by
    let T:= F.level h; refine trustee_board T L ((F.level h).starts_unit.symm ▸ hu) (fun d a x y=> ?_) p v
    let q : Label G d:=⟨x.val,y⟩; rw [show x=raiseLabel G a q from rfl,← (F.level d).basis.sum_repr q]; simp_rw [map_sum,map_smul, ←climb]; apply Submodule.sum_mem; intro i _; apply Submodule.smul_mem; have h:wt (F.level h) (upL F a i)≤d:= (congr_arg Prod.fst (up_grade F a i)).trans_le ((F.level d).bound i); exact Maxwell.Free.chain h (H (upL F a i))
-- scale & signed natural on mesh-local expressions
lemma vista_real (i:(F.level h).Index): Normalize.reel h (vista F i)= vista F i:= by rw [carried]; apply Eq.symm; have hx:= (F.level h).realForm i; refine Subtype.ext (show Maxwell.observable G h ((F.level h).basis i)=_ from (?_)); have he:= Maxwell.Free.real_eats ((F.level h).basis i); rw [hx] at he; exact he
lemma vista_spinner (s:Signed)(i:(F.level h).Index): Normalize.ori s.ortho h (vista F i)=∑ j,(↑(realM Rι s j i):ℂ) • vista F j:=by
    simp_rw [carried]; let L:=bulb G h; let Q:=F.level h; set x:= Labels.tensor s.ortho (Q.basis i); rw [← show L x= Normalize.ori s.ortho h (bulb G h ((F.level h).basis i)) from Subtype.ext (Maxwell.Free.pulls_label (Q.basis i) s.ortho)]; nth_rw 1 [← Q.basis.sum_repr x]; rw [map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [map_smul]; change Q.coords x j • _=_; rw [show Q.coords x=_ from (Q.act_coords s.ortho (Q.basis i)).symm,Q.coords_basis]; exact congr_arg (fun c:ℂ=> c • bulb G h ((F.level h).basis j)) (bleach_even Rι s.ortho j i)
lemma tapeHeight (V:Normalize.Guard G h)(p:Formal V)(i:ℕ):
    (∀ d≤h,∀ x∈ Folia G d h, coeff i V x ∈ Folia G d h)∧
    (∀ x, coeff i V (Normalize.reel h x)=Normalize.reel h (coeff i V x))∧
      (∀ s:Signed, ∀ x, coeff i V (Normalize.ori s.ortho h x)=Normalize.ori s.ortho h (coeff i V x)):=by
       obtain ⟨u,rfl⟩:= p.actions; rw [Normalize.decked,Normalize.pulling]; split_ifs with hi; · exact ⟨fun d a x v=> Submodule.add_mem (Folia G d h) v ((u i).property.2.1 d a x v),fun x=>(Normalize.stood_reel ..).symm,fun s x=>(Normalize.stood_ori ..).symm⟩
       exact (u i).property.2
lemma leafFormal (V:Normalize.Guard G h)(p:Formal V)(x:InkQ): respond (facet V) (Tape.side (Normalize.leaf G h) x)=Tape.side (Normalize.leaf G h) x:=by
    obtain ⟨u,rfl⟩:= p.actions; rw [respond_side]; let Q:=Normalize.deck u; let F:=Normalize.leaf G h; rw [show spur (facet Q) F=Tape.side F 1 from (?_), starE_side,mul_one]; funext i; rw [side_read,coeff_one]; change coeff i Q F= _; unfold Q; rw [Normalize.decked,Normalize.pulling]; split_ifs; rw [Normalize.solitary,one_smul]; rw [show (u i).val F=0 from (u i).property.1,zero_smul]
lemma tempoF_real (x: Tape (Sec G h))(v:WReal x)(c:InkQ)(p:realInk c) : WReal (tempo c x):=by
    intro i; simp only [tempo,LinearMap.coe_mk,AddHom.coe_mk,map_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [(Normalize.reel h).map_smulₛₗ, show starRingEnd ℂ _=_ from realLevel _ (polR _ p j) i,v]
lemma frame_real (V:Normalize.Guard G h)(p:Formal V)(x:Tape (Sec G h))(v:WReal x) : WReal (respond (facet V) x):=by intro i; simp only [Tape.respond,LinearMap.coe_mk, AddHom.coe_mk,map_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [facet,← (tapeHeight V p j.1).2.1, v]
lemma frame_height (V:Normalize.Guard G h)(p:Formal V)(x:Tape (Sec G h))(v:∀ i,x i∈ Folia G d h) (z:d≤h)(c: InkQ) (i:ℕ): tempo c (respond (facet V) x) i∈ Folia G d h:=by
   simp only [tempo, Tape.respond, LinearMap.coe_mk, AddHom.coe_mk]; apply Submodule.sum_mem; intro j hj; apply Submodule.smul_mem; exact Submodule.sum_mem _ (fun i h=> (tapeHeight V p i.1).1 _ z _ (v _))
lemma tempo_spin (s:Signed)(V:Normalize.Guard G h)(p:Formal V)(x:Tape (Sec G h))(c:InkQ): Tape.layer (Normalize.ori s.ortho h) (tempo c (respond (facet V) x))=tempo c (respond (facet V) (Tape.layer (Normalize.ori s.ortho h) x)):=by
    let v:= fun i x=> (tapeHeight V p i).2.2 s x; funext i; simp only [tempo,Tape.layer,Tape.respond,LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [map_sum,map_smul,facet,v,map_sum] -- inspect
end prime
end Stair
end YM.WilsonCoeffUV.Mer.Xa
