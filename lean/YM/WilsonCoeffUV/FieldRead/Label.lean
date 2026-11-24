import YM.WilsonCoeffUV.FieldRead.Color
import Mathlib.LinearAlgebra.Projection

/-! Outcrops from same analytic `localFields` reference. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 45000
noncomputable section
namespace YM.WilsonCoeffUV.Fountain
open Filter Function Set Laurent Lattice RG Exterior Precision Next.Free Gauge Power
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l m n p:ℕ}{A C s t :ℝ}

def castP (F:Glas G h l): Tensor.T (Snap G h) ℂ l:= Complex.ofRealCLM.compContinuousMultilinearMap (latent F)
def vein (F:Glas G h l)(J:Labels.Jet G)(t:ℝ): ℝ:= Tensor.diagonal (latent F) (engineered t (trunk h J))
def seedTile (F:Glas G h l)(n:ℕ): Pol G:= tile (castP F) n
lemma vein_smooth (F:Glas G h l)(J:Jet G)(n:ℕ): ContDiff ℝ (↑n) (vein F J):= (Tensor.diag_smooth ..).comp (eng_cont (trunk h J) _)
lemma reads_seedTile (F:Glas G h l)(n:ℕ)(J: Jet G): (read J) (seedTile F n)= (leading n (vein F J):ℝ):=by
   let L:= Complex.ofRealCLM
   rw [seedTile,←tile_reads]; change (n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n (L ∘ vein F J) 0 _ = L ((n.factorial:ℝ)⁻¹ • iteratedDeriv n (vein F J) 0)
   rw [L.iteratedFDeriv_comp_left (vein_smooth F J n).contDiffAt le_rfl,L.map_smul]; rfl
lemma seed_real (F:Glas G h l)(n): conjPol (seedTile F n) = seedTile F n:= eval_ext _ _ fun J=>by rw [conj_value,reads_seedTile]; simp
lemma seed_grade (F:Glas G h l)(n): pureDegree (seedTile F n) n l := tile_grade ..
lemma seed_limited (F:Glas G h l) (hp:n≤h): seedTile F n ∈ limited G h:=by
    apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
    intro i hi; have he:=seed_grade F n (MvPolynomial.mem_support_iff.mp hi); rw [weight_slot] at he; exact (show height i=n from congr_arg Prod.fst he).trans_le hp
lemma secret (F: Glas G h l)(J:Jet G): vein F J=fun t=> Tensor.diagonal F (casing G h (engineered t (trunk h J))):=rfl

-- ℂ Pol G as AddComm, extend restricted complex coefficient extraction via split
lemma seeding_sum (F T:Glas G h l)(n:ℕ): seedTile (F+T) n=seedTile F n+seedTile T n:=by
    apply eval_ext; intro J; rw [map_add]; simp_rw [reads_seedTile,←Complex.ofReal_add]; congr 1; unfold leading
    rw [show vein (F+T) J=fun t=> vein F J t+vein T J t from rfl,iteratedDeriv_fun_add (vein_smooth F J n).contDiffAt (vein_smooth T J n).contDiffAt,smul_add]
lemma seeding_scale (F:Glas G h l)(c:ℝ)(n:ℕ): seedTile (c•F) n= (c:ℂ) • seedTile F n:=by
    apply eval_ext; intro J; rw [map_smul]; simp_rw [reads_seedTile]; rw [smul_eq_mul,←Complex.ofReal_mul]; congr 1
    exact lead_sc (vein_smooth F J n).contDiffAt c
lemma seeding_empty (G:Gauge)(l n h:ℕ): seedTile (0:Glas G h l) n=0:=by
    simpa only [zero_smul,Complex.ofReal_zero] using seeding_scale (0:Glas G h l) 0 n

lemma seed_paint (H:Hol G)(c:Volume D){F:ChamberTen G (Vote D) r}(q:Twig 0 s A F)(hc:0<s)(ht:mural F) (h l:ℕ)(he:n≤h): seedTile (arret c F h l) n∈ localFields G h := by
    refine ⟨seed_limited _ he,?_⟩; intro J u
    rw [reads_seedTile,reads_seedTile]; congr 2; funext x; unfold vein; rw [show engineered x (trunk h (colored u J))= Cast u (engineered x (trunk h J)) from Eq.symm <| funext fun i=> map_smul (Taylor.paint u) (x^(i.val+2)) (trunk h J i)]; exact arret_mural c H q hc ht u _

private def canteen (G:Gauge)(h l n:ℕ): Submodule ℝ (Glas G h l) where
    carrier:={F| seedTile F n∈localFields G h}
    zero_mem':= by change seedTile (0:Glas G h l) n∈localFields G h; rw [seeding_empty]; exact Submodule.zero_mem _
    add_mem':= fun {a b} e t=> by change seedTile (a+b) n∈ localFields G h; rw [seeding_sum]; exact (localFields G h).add_mem e t
    smul_mem':= fun c a e=> by change seedTile (c • a) n∈ localFields G h; rw [seeding_scale]; exact (localFields G h).smul_mem _ e
lemma searcher (F: Frame G h)(l n:ℕ): ∃ L:Glas G h l→L[ℝ] F.Coeff,∀ x:Glas G h l,∀ h:seedTile x n∈localFields G h,L x=F.coords ⟨seedTile x n,h⟩:=by
   let V:=canteen G h l n
   obtain ⟨p,hp⟩:= V.exists_isCompl
   let f:V→ F.Coeff:= fun x=> F.coords ⟨seedTile x.val n,x.property⟩
   let a: V →ₗ[ℝ] F.Coeff:={
       toFun:=f
       map_add':= fun x y=> by
          unfold f; rw [← map_add]; apply congr_arg F.coords; exact Subtype.ext (seeding_sum ..)
       map_smul':= fun c x=> by
          change f _=c•f x; rw [show c•f x=(c:ℂ) • f x from ?_]; swap; · ext; rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul]; rfl
          unfold f; rw [←map_smul]
          apply congr_arg F.coords; exact Subtype.ext (seeding_scale ..) }
   let L:= a.comp (Submodule.projectionOnto V p hp)
   refine ⟨L.toContinuousLinearMap,fun x e=>?_⟩; change a (V.projectionOnto _ hp x) = _; rw [Submodule.projectionOnto_apply_of_mem_left hp (show x∈V from e)]; rfl

def Bell (F:Frame G h)(n l:ℕ): Glas G h l→L[ℝ] F.Coeff:= (searcher F l n).choose
lemma detecting (F:Frame G h)(x:Glas G h l)(n)(hx:seedTile x n∈localFields G h): Bell F n l x=F.coords ⟨seedTile x n,hx⟩:=(searcher F l n).choose_spec ..
lemma bell_mood (F:Frame G h)(x:Glas G h l)(n)(hx:seedTile x n∈localFields G h): star (Bell F n l x)=Bell F n l x := by
   rw [detecting _ _ _ hx]; funext i; rw [Pi.star_apply,← Frame.conj_basis,F.coords.symm_apply_apply]; rw [show realBar (⟨_,hx⟩:Label G h)=⟨_,hx⟩ from Subtype.ext (seed_real ..)]
lemma bell_coral (F:Frame G h)(x:Glas G h l)(n)(hx:seedTile x n∈localFields G h)(i:F.Index)(t:(n,l)≠F.grades i): Bell F n l x i=0:=by rw [detecting _ _ _ hx]; exact F.power_coefficient i t (seed_grade ..)
lemma seam (P:Frame G h)(H:Hol G)(c:Volume D)(n l:ℕ)(he:n≤h)(σ:Signed)(F T:ChamberTen G (Vote D) r)(a:alliance σ F T)(p:Twig 0 s A F)(q: Twig 0 t C T)(hs:0<s)(ht:0<t)(hu:mural F)(hv:mural T): Bell P n l (arret c T h l)=P.act σ.ortho (Bell P n l (arret (spinV σ D c) F h l)):=by
    rw [detecting _ _ _ (seed_paint H _ q ht hv h _ he), detecting _ _ _ (seed_paint H _ p hs hu h _ he), P.act_coords];
    apply congr_arg P.coords; apply Subtype.ext; apply eval_ext; intro J
    change read J _=read J (rotated _ _); rw [rotated,eval_changed]; simp_rw [reads_seedTile]; congr 2; funext x
    unfold vein; rw [follows H σ F T a c _ p q hs ht]; congr 1
    exact funext fun i=> map_smul (Taylor.turn (G:=G) σ.ortho⁻¹) (x^(i.val+2)) (trunk h J i)
end YM.WilsonCoeffUV.Fountain
