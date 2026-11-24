import YM.Qlocal.Feud.AmberP
/-! # Emit Θ aromatic.N.Canvas.A.Capped projection term. Preserving authentic consumer order.
 Kernel forecast may also include coupling reset in further proofs; this P≈R' furnished before shift.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Kinetic
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
namespace Peak
open Quipu Quipu.Tilt Quipu.Sonnet Tern Quipu.Eluder Incline Incline.Bookworm
open Extra.Iteration Bind
open Catch Aux.Name Poll
variable {G:Gauge} {k j m i q r n:ℕ} {c f :Side}{b b' a α δ t:ℝ}
variable {ι σ:Type*}{V:Type}[DecidableEq V]{Z:Marker.Census V}
variable (Z0 : Catch.Clock ι) {P:Patch}{K:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F₀:Uniform.Before G v.width v.paths P.J K (k+3+3)}
variable (W:ι→ Aux.Name G P K u κ v (k+3) F₀) (d:ι→ℝ)(x:∀ i,(W i).X)
variable (g:V→ℕ) (o:∀ i:ι,V→Site (W i).c) (s:Senses Z) (A:ι→Stanza Z G g m)(N:ℕ)
local notation "L"=>Z0.rail
local notation "U"=>Stanza.son
set_option quotPrecheck false
local notation "P[" i "]"=> Stanza.son (A i) N
local notation "snap"=> scene W g m N A (fun i=> Anthem.statement (Stanza.son (A i) N)) s o
variable (Y:∀ i,(W i).X→ Word ℝ) (Gv:ι→ℝ)
local notation "rankm"=> Lagger.dues g s.val
local notation "w"=> fun i:ι=> (W i).Θ
local notation "Γ"=> Catch.Cover Z0 j
local notation "Ψ"=> Peak.token W snap
local notation "X[" i "]"=> (W i).X
local notation "ε"=>fun i=> (d i)⁻¹
variable (hT:Aux.Name.Proper W Z0)(K_σ:ι→ℝ) (ha:∀ i, ((A i).son N).Allows (α+b') (K_σ i))(hz:0<α)(hb:0 ≤ b') (h0:∀ᶠ i in Z0.rail,0<d i)(hK:Z0.Meter d (-(1/2:ℝ)))(hx:Z0.Meter (fun i=> ‖x i‖) (-(1/2:ℝ)))
variable (hC : Z0.Meter K_σ 0) (he:∀ i≤r,∃ P':ι→ℝ, Z0.Meter P' δ ∧∀ᶠ j in Z0.rail,Expectations W g o s A N Y P' i j) -- phase.Wait
local notation "Pℓ"=>imprint W snap rankm
local notation "Φ"=> Canopy.Lithe.beam (Ψ rankm) r w
local notation "J₀"=> Canopy.Lithe.beam Y r w
include hT ha hz hb h0 hK hx he
lemma estimates : Catch.Cover Z0 j δ ε (Φ-J₀) x:= by
 let f(k:ℕ) i (x:X[i]):= Peak.token W snap rankm i x k- Y i x k; have hv(k:ℕ)(hk:k≤r): Catch.Cover Z0 j δ ε (fun i=> (w i)^k • f k i) x:= by
      obtain ⟨V',hv,hh⟩:= he k hk; refine (((income_w Z0 W d x g o s A N Y V' hT K_σ ha (add_pos_of_pos_of_nonneg hz hb) h0 hK hx hv hh (j:=j)).caliber (hT.meter W|>.1.pow k)).weak (?_)); push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) k] -- unfold graded? not present.
 apply Catch.Cover.home (Catch.Cover.booking _ (fun j h=>hv j (Nat.le_of_lt_succ (Finset.mem_range.mp h))) (h0.mono fun _ hi=> inv_nonneg.mpr hi.le)); filter_upwards with i; ext1 x; simp only [Finset.sum_apply,Pi.sub_apply, Canopy.Lithe.beam, PositionX.Jet.delay,f,Pi.smul_apply,smul_sub,Finset.sum_sub_distrib] -- weird range infer
include hC
variable (b0:ι→ℕ)
local notation "S"=>fun i=> Anthem.statement ((A i).son N)
local notation "k0"=>husk g m N A (S) b0
local notation "Pq"=> scene W g m N A k0 s o
local notation "Zκ"=>fun i=>Cider.nod b' (b0 i)
variable (hh: Z0.Meter (fun i=>Cider.nod b' (b0 i)) (graded (r+Lagger.dues g s.val+1))) -- syntax tune later
include hh
lemma prediction (hl:Lagger.dues g s.val+r<j) (hd:δ≤ graded (r+1)) : Γ (graded (r+1)) ε (imprint W Pq rankm-J₀) x:= by
 have hx1:= hx.weak (show -(1/2:ℝ)≤ graded 1 by simp [graded])
 let H':= fastened (j:=j) W g m N A (S) K_σ ha hz hb hC s o; let hA i:= (P[i]).quartile s (o i) (ha i) (add_pos_of_pos_of_nonneg hz hb) (Anthem.statement (P[i])); have hS:= Peak.paints W snap hT d x hK h0 hx1 H' hA hl; have hP:= (estimates (j:=j) Z0 W d x g o s A N Y hT K_σ ha hz hb h0 hK hx he); let Hℓ i:= scene W g m N A k0 s o i; have ht:= Peak.shave W snap hT d x hK h0 hx1 (scene W g m N A k0 s o) Zκ hh (sharp (j:=j) W g m N A S K_σ ha hz hb hC s b0 o)
 apply Catch.Cover.home (((hS.add (hP.weak hd))).sub ht); filter_upwards with i; ext1 x; dsimp only [Pi.sub_apply, Pi.add_apply]; abel
end Peak
end YM.Qlocal.Feud
