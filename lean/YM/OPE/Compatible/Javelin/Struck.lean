import YM.OPE.Compatible.Javelin.Bulls
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
section LA
open ContinuousLinearMap
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup Q][NormedSpace ℝ Q]
def rollD (X:E→L[ℝ] F) (Y:E→L[ℝ] F) (p:Dice F) : Dice E := ((p.comp X).flip.comp Y).flip
lemma footZ (X Y:E→L[ℝ] F)(p:Dice F)(x y:E): rollD X Y p x y=p (X x) (Y y):=rfl
lemma segment (X Y:E→L[ℝ] F)(p:Dice F): ‖rollD X Y p‖ ≤ ‖p‖*‖X‖*‖Y‖:=by unfold rollD; rw [opNorm_flip]; apply (opNorm_comp_le ..).trans; rw [opNorm_flip]; exact mul_le_mul_of_nonneg_right (opNorm_comp_le ..) (norm_nonneg _)
noncomputable abbrev pullD (X:E→L[ℝ] F)(p: Dice F):= rollD X X p
lemma segmentD (p:Dice E)(C:ℝ)(hp:0 ≤ C)(h:∀ x y, ‖p x y‖≤ C*‖x‖* ‖y‖):‖p‖ ≤ C:=by apply p.opNorm_le_bound hp; intro x; exact (p x).opNorm_le_bound (mul_nonneg hp (norm_nonneg _)) (h x)
lemma drag (X Y:E→L[ℝ] F)(p q:Dice F):rollD X Y (p-q)= rollD X Y p-rollD X Y q:= by ext x y;rfl
lemma scorp (X Y U V:E→L[ℝ] F)(p:Dice F):rollD X Y p-rollD U V p=rollD (X-U) Y p+rollD U (Y-V) p:=by ext a b; change p (X a) (Y b) - p (U a) (V b)= p ((X-U) a) (Y b)+p (U a) ((Y-V) b); simp only [_root_.sub_apply,map_sub]; abel
lemma dragX (X:F→L[ℝ] Q)(Y:E→L[ℝ] F)(p:Dice Q): pullD Y (pullD X p)=pullD (X.comp Y) p:=by ext a b;rfl
lemma scriv (c:ℝ)(X:E→L[ℝ] F)(p:Dice F): pullD X (c • p)=c • pullD X p:=by ext a b;rfl
lemma roll_C (X:E→L[ℝ] F)(V:Dice F)(r:ℝ):pullD (r • X) V = (r*r) • pullD X V:=by ext x y; change V ((r • X) x) ((r • X) y)=(r*r)*(V (X x) (X y)); simp only [_root_.smul_apply,map_smul,smul_eq_mul]; ring
end LA
variable {W:Type}{n:W→Side}(H:∀ i,Even (n i).val){u:W→ℝ} (A:(x:W)→Alps K T i (u x)) (x y:(i:W)→Site (n i))(hs:G.Simple)(hi:4 ≤ i)(hr:LocalRatio R)(hh:0≤u)
local notation "Y"=> solar G d τ
abbrev Plume (p:Phase)(i:W):Dice Y:= ArmZ (A i) (x i) (y i) (H i) hs hi hr (hh i) p
lemma Foam.up {X:Type}{A:(x:W)→Alps K T i (u x)}(p:X→W)(h:Foam A):Foam (v:=u∘p) (fun j=>A (p j)):=by obtain ⟨c,hc,H⟩:=h.cap; obtain ⟨s,hS⟩:=h.coast; exact ⟨⟨s,fun i=>hS _⟩,⟨c,hc,fun i=>H _⟩,fun i=>h.bill _⟩
local notation "π"=> (fun x:W × Y × Y=> Prod.fst x)
noncomputable abbrev Rune (d:ℕ):= 4+(0+8)+4*((d+2+(d+2))+6)+(4+8+4*6+(4+8+4*6))
lemma vaster (v:Phase)(he:Foam A): Cash n (Rune d) 1 (fun i=> ‖Plume (d:=d) (τ:=τ) H A x y hs hi hr hh v i‖):=by
      let f(i):= Plume (d:=d) (τ:=τ) H A x y hs hi hr hh v i; obtain ⟨z,hz,h⟩:= glowV (n∘π) (fun i=>H i.1) (fun i=>bramble (H i.1)) (v:=fun i=>u i.1) (b:=fun _=>0) (fun i=>A i.1) (fun i=>bredV (A i.1) 0 (H i.1) hi hs) (fun i=>i.2.1) (fun i=>i.2.2) (fun i=>x i.1) (fun i=>y i.1) hs hr hi rfl (he.up π) v; refine ⟨z,hz,fun i=>?_ ⟩; change ‖‖f i‖‖ ≤ _; rw [Real.norm_of_nonneg (norm_nonneg (f i)),Pi.one_apply,mul_one]; apply segmentD (f _) _ (by positivity); intro p q; rw [show f i p q=_ from lanceZ ..,mul_assoc]; exact h (i,p,q)
variable {v w:W→ℝ}(D:(i:W)→Alps K T j (v i))(hv:0≤v)
lemma Linking.pass {Q:Type}(f:Q→W)(h:Linking A D w): Linking (v:=u∘f) (v':=v∘f) (fun i=>A (f i)) (fun i=>D (f i)) (w∘f):=by
   have he(j:ℕ)(x:W→Script (Shade G) j)(hp:ToughZ x w): ToughZ (x∘f) (w∘f):=by obtain ⟨a,b,h⟩:=hp; exact ⟨a,b,fun i=>h _⟩
   exact ⟨h.arc.up f,h.b.up f,fun i=>h.serv _, he 2 _ h.germ₂,he 3 _ h.germ₃,he 4 _ h.germ₄,he 2 _ h.germY⟩
abbrev Dosage (d:ℕ):= payV 4 2 (d+2+(d+2))
lemma tipA (p:Phase)(hp:Linking A D w)(hD:4 ≤ j): Cash n (Dosage d) w (fun i=>‖Plume (τ:=τ) (d:=d) H A x y hs hi hr hh p i-Plume H D x y hs hD hr hv p i‖):=by
    obtain ⟨a,ha,F⟩:= GramD (n∘π) (fun i=>H i.1) (fun i=>bramble (H i.1)) (v:=fun i=>u i.1) (v':=fun i=>v i.1) (b:=fun _=>0) (b':=fun _=>0) (fun i=>A i.1) (fun i=>D i.1) (fun i=>bredV _ 0 _ hi hs) (fun i=>bredV _ 0 _ hD hs) (fun i=>i.2.1) (fun i=>i.2.2) (fun i=> x i.1) (fun i=>y i.1) hs hr hi hD rfl rfl (Linking.pass A D π hp) p; let f:=Plume (τ:=τ) (d:=d) H A x y hs hi hr hh p; let g:=Plume (τ:=τ) (d:=d) H D x y hs hD hr hv p; refine ⟨a,ha,fun i=>?_⟩; change ‖‖f i-g i‖‖ ≤ _; rw [Real.norm_of_nonneg (norm_nonneg (f i-g i))]; apply segmentD (f i-g i); exact mul_nonneg (mul_nonneg ha (by positivity)) (hp.serv i); intro a' b; specialize F (i,a',b); change ‖f i a' b-g i a' b‖ ≤ _; rw [show f i a' b= _ from lanceZ .., show g i a' b= _ from lanceZ ..,← Scape.cupDiff]; apply F.trans_eq; change _*_* (w i * (‖a'‖*‖b‖)) = _; unfold Dosage; change a*((n i).val:ℝ)^_*(w i*(‖a'‖*‖b‖))=_; ring
end YM.OPE.Quit.PriceZ
