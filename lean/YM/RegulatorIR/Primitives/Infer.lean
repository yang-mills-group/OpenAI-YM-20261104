import YM.RegulatorIR.Primitives.Cinder

/-!
# Native joint penalty stencil – genuine StepData
Re-derive Taylor vertices from simultaneous field extraction, tree chosen by
elimination applies to fine field values later. Wrap universality covers
repeated patch visits and lifted predictor fallback. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Chart Gauge RG Orb Laplace Tree Precision Push
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {I:Type}{G:Gauge}{f c:Side}
variable (S:StepData c f)(Z:S.patch.Branches S.kernel G)

abbrev KFoot (G:Gauge):= Foot G⊕ Foot G

lemma grass (d:Motion): S.patch.L.val • baseR c d= baseR f d:=by cases d <;> rw [baseR, baseR, smul_smul,S.sizes,Nat.mul_comm]
include Z
lemma polar_pull (U:CoverConfig G): pond S.patch S.kernel (pull invS 0 U)=pull invS 0 (pond S.patch S.kernel U):=by
 ext1 i
 rw [chilled Z,pull,affine,pivot_dir,add_zero];rfl
omit Z in
lemma distant (s: Signed)(U :CoverConfig G)(t:Cover) : pull s t U = pull s 0 (translate t U):=by
 rw [← pull_one,pull_pull, one_mul];simp [affine]
lemma circle (d:Motion) (U:CoverConfig G): pond S.patch S.kernel (pull (parity d) (baseR f d) U)=pull (parity d) (baseR c d) (pond S.patch S.kernel U):=by
 cases d with
 | across v=> rw [← grass S, parity,pull_one,pull_one, pulled]
 | turn v=> rw [parity, distant,distant invS _ (baseR c _)] -- need parity first
            rw [← grass S, polar_pull S Z,pulled]
omit Z
variable (N:Scale)
def opi (N:Scale)(i:Edge Cover):Micro (KFoot G):= fun t x=> N.beta t*S.kernel.penalty*G.price (win G (x ∘ Sum.inr) i*(pond S.patch S.kernel (win G (x ∘ Sum.inl)) i)⁻¹)
include Z

variable {l R P:ℝ}(H: Even f.val)(he:Even c.val)(hr:l*f.val=P)(hs:R*c.val=P)
local notation "C0" => Carto G l P H hr
local notation "C1" => Carto G R P he hs
local notation "D0" => Step.combine C0 C1
lemma footing : Offset D0 (posMarch he) (opi S N):=by
 intro d i t w; let T:=toolP D0 d w; let y:= (posMarch he).rips d i
 let U:=win G (w ∘ Sum.inl); let V:=win G (w∘ Sum.inr); let A:=win G (T∘ Sum.inl); let B:=win G (T∘ Sum.inr)
 have hu: pull (parity d) (baseR f d) A=U:= tools_links H hr d (w∘ Sum.inl)
 have hp: pull (parity d) (baseR c d) B=V:= tools_links he hs d (w∘ Sum.inr)
 let Ψ:= pond (G:=G) S.patch S.kernel
 have hh:= circle S Z d A; rw [hu] at hh
 have hi:= congr_fun hp i
 change N.beta t * S.kernel.penalty* G.price (B y*(Ψ A y)⁻¹)= N.beta t * S.kernel.penalty * G.price (V i*(Ψ U i)⁻¹)
 apply congr_arg; rw [show Ψ U i=(pull _ _ (Ψ A)) i from congr_fun hh i,
     ← show pull _ _ B i=V i from hi,lifted,lifted];cases d
 · rfl
 change G.price (B y * (Ψ A y)⁻¹)= G.price ((B y)⁻¹*((Ψ A y)⁻¹)⁻¹); rw [inv_inv,← G.price_inv ((B y)⁻¹*_),show ((B y)⁻¹*_)⁻¹= (Ψ A y)⁻¹*(B y*(Ψ A y)⁻¹)*((Ψ A y)⁻¹)⁻¹ by group,G.price_conj]
lemma settledLow (i:Edge Cover) : pond (G:=G) S.patch S.kernel (1:CoverConfig G) i=1:=by
 rw [show (1:CoverConfig G)= (1:Config G f) ∘ around f from rfl,river (S:=S),Push.settled S Z]
lemma opi_zero (p:Edge Cover) t: opi (G:=G) S N p t 0=0:=by
 have hx: win G 0=1:=by ext1 i;unfold win; rw [timber_0]; exact G.mat_lieExp_zero
 unfold opi; rw [show (0:KFoot G→ℝ)∘ Sum.inl=0 from rfl,show (0:KFoot G→ℝ)∘ Sum.inr=0 from rfl,hx,settledLow S Z]; simp
omit Z H he hr hs

-- local Taylor existence via finite scaffold of same algorithm
section Local
attribute [local instance] Gauge.frobInner
variable (G) (I:Type)

def picker (p:I↪ KFoot G)(a: Edge Cover)(h:Bool): (I→ℝ)→ₗ[ℝ] G.Color where
 toFun:=fun x=> timber G ((liftFill p x)∘ (if h then Sum.inl else Sum.inr)) a
 map_add' u v:=by rw [map_add];rfl
 map_smul' r u:=by rw [map_smul];rfl

-- install arbitrary finitely-many edges on enlarged torus B
variable {G I}
def plant {L:Finset (Edge Cover)}{n:Side}(h:Set.InjOn (around n) (L:Set (Edge Cover)))(v:↥L→(I→ℝ)→ₗ[ℝ] G.Color): (I→ℝ) →ₗ[ℝ] (Edge (Site n)→G.Color):=
 LinearMap.pi (Function.extend (ascend L n h) v (fun _=>0))
lemma clipping {L:Finset (Edge Cover)}{n:Side}(h:Set.InjOn (around n) (L:Set (Edge Cover)))(v:↥L→(I→ℝ)→ₗ[ℝ] G.Color)(i:↥L) (x) : plant h v x (around n i.val)=v i x:= congr_arg (fun T:(I→ℝ)→ₗ[ℝ] G.Color=>T x) ((ascend L n h).injective.extend_apply (g:=v) (e':=fun _=>0) i)

include Z
lemma lodi (E:Finset (KFoot G))(i:Edge Cover) : ContDiffAt ℝ ω (fun w:↥E→ℝ=> G.mat (pond S.patch S.kernel (win G (fill (placeFin E) w ∘ Sum.inl)) i)) 0:=by
 let F:=(placeFin E); let L:= lantern S.patch i; obtain ⟨n,h⟩:= ampleS S.patch L;let M:= canopy S n
 let p:=n*S.patch.L; let v (a:↥L):= picker G _ F a.val true;let X:(↥E→ℝ) →ₗ[ℝ] In G p:=LinearMap.pi (fun k: Exterior.Body 1 p=> (LinearMap.proj (k.1,Exterior.axisEquiv.symm k.2)).comp (plant h v))
 have hz w : pond S.patch S.kernel (win G (fill F w ∘ Sum.inl)) i=M.prediction (represent (X w)) (directive M) (around n i):=by
    rw [show M=canopy S n from rfl,← sunset];apply pond_low S.patch S.kernel Z _
    intro e he; rw [Function.comp_apply,Work.F03.represent_link];unfold win; apply congr_arg
    change _=plant h v w (_,Exterior.axisEquiv.symm (Exterior.coord _)); rw [show ∀ i:Axis,Exterior.axisEquiv.symm (Exterior.coord i)=i from fun i=>Exterior.axisEquiv.symm_apply_apply i]; exact (clipping h v ⟨e,he⟩ w).symm
 simp_rw [← show F=placeFin E from rfl,hz];exact ContDiffAt.comp (f:=⇑X) _ (show ContDiffAt ℝ ω (fun x=>G.mat (M.prediction (represent x) (directive M) (around n i))) (X 0) from (map_zero X).symm ▸ Push.prediction_cont M Z ..) X.toContinuousLinearMap.contDiff.contDiffAt
lemma locally (i : Edge Cover) : Nonempty (Run (opi (G:=G) S N i)):=by
 let R:= lantern S.patch i; let E:= ((R×ˢ Finset.univ).image (Sum.inl:Foot G→KFoot G))∪Finset.univ.image (fun a:G.ColorIndex=>Sum.inr ((i,a):Foot G)); let F:=placeFin E
 refine ⟨{ J:=↥E,fin:=inferInstance,inc:=F,script:=fun t=> opi S N i t.1 (fill F t.2),smooth:=?_,reaches:=?_ }⟩
 · let W (w:↥E→ℝ):= (win G (fill F w ∘ Sum.inr) i*(pond S.patch S.kernel (win G (fill F w∘ Sum.inl)) i)⁻¹)
   apply ContDiffAt.mul ((N.near.comp (f:=Prod.fst) (0:ℝ × (↥E→ℝ)) contDiffAt_fst).mul contDiffAt_const)
   have hh: ContDiffAt ℝ ω (fun w=>G.price (W w)) 0:=by
      apply Work.F03.price_smooth; simp only [W,G.mat_inv,G.mat_mul]; apply ContDiffAt.mul
      · exact G.exp_jet.contDiffAt.comp _ (picker G _ F i false).toContinuousLinearMap.contDiff.contDiffAt
      exact (starL' ℝ).contDiff.contDiffAt.comp _ (lodi S Z E i)
   exact (hh.of_le le_top).comp (f:=Prod.snd) (0:ℝ× (↥E→ℝ)) contDiffAt_snd
 intro t x
 let w:=fill F (x ∘ F)
 have he : win G (x ∘ Sum.inr) i=win G (w ∘ Sum.inr) i:=by
    apply congr_arg G.lieExp; ext1 j;exact (fill_eq E (.inr (i,j)) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)) x).symm
 have hp: pond S.patch S.kernel (win G (x ∘ Sum.inl)) i=pond S.patch S.kernel (win G (w ∘ Sum.inl)) i:=by
    apply pond_low S.patch S.kernel Z; intro a ha;apply congr_arg G.lieExp; ext1 j; exact (fill_eq E (.inl (a,j)) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a,j),Finset.mem_product.mpr ⟨ha,Finset.mem_univ _⟩,rfl⟩)) x).symm
 exact congr_arg (fun r:G.El=>N.beta t*S.kernel.penalty *G.price r) (congr_arg₂ (·*·) he (congr_arg Inv.inv hp))
end Local
end YM.RegulatorIR.Prim
