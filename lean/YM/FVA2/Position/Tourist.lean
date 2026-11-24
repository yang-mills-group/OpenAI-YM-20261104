import YM.FVA2.Position.Brass
/-!
# Open-index Jrad prescription (`OpenAxis`): action of `Signed`

Take the specific lift (see `Press/Deck.lean`) and continuation
in `MS_Data`; we want its orientation known exactly. Kernel action is by precomposition
(opposite action). See `equivariant`. Later use this in building compatible mark fees.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Position.OpenAxis
open Function Set Filter Finset
open MS MS.Plane MS.Arts MS.Arts.Spin MS.Landau MS.Landau.Detect MS.Momentum MS.Koszul
open MS.Outlook MS.Halo MS.Motif MS.Theater Labels
open Brass Weft
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace Classical
variable {m n k:ℕ}{G:Gauge} (s t:Signed){x:E4}{a b:Axis}{z:ℂ}
abbrev survey (G:Gauge)(m:ℕ):= Surf.orbit (viewD s m) G
local notation "σ" => survey s G m
lemma gone {E:Type}[AddCommMonoid E][Module ℂ E](V:L m→ E)(a:Axis) : ∑ j:L m, (σ).profile j (chair m (s.perm a)) • V j= (sig s a:ℂ) • V (chair m a):= by
    unfold survey Surf.orbit; simp only [pore,apply_ite Complex.ofReal, Complex.ofReal_zero,ite_smul,zero_smul]; -- check Complex.ofReal or ofReal ...
    simp
lemma cur_slide (a b:Axis): (σ).air (cur z (chair m (s.perm a)) (chair m (s.perm b)))= sig s a • sig s b • cur z (chair m a) (chair m b):= by rw [ Surf.earth, gone,gone ]; rfl
lemma walk (X:Mield G m)(a:Axis): (σ).air (convoke z (chair m (s.perm a)) X)= sig s a • convoke z (chair m a) ((σ).air X):= by rw [Surf.grip,gone]; rfl
local notation "R"=> Ortho.move s.ortho
private lemma air_p (X:Mield G m)(c:ℝ): (σ).air (c • X)=c • (σ).air X:= map_smul ((Surf.air σ).restrictScalars ℝ) c X
lemma ray_top (a b:Axis)(k:ℕ): (σ).air (graft z (s.perm a) (s.perm b) (R x) k)= sig s a • sig s b • graft z a b x k := by
 induction k with
 | zero=>exact cur_slide ..
 | succ n ih=> rw [graft,graft,map_sum]; simp_rw [air_p, Finset.smul_sum]; rw [← Equiv.sum_comp s.perm]; apply Finset.sum_congr rfl; intro j _; rw [ax_v, walk,ih]; let L:= (graft z a b x n: Mield G m ); let Q:= (convoke (G:=G) z (chair m j)).restrictScalars ℝ; have ht(U:Mield G m)(z':ℝ): convoke z (chair m j) (z' • U)=z' • convoke z (chair m j) U:= map_smul Q z' U; rw [ht,ht, mul_comm (sig s j),mul_smul,sig_t,smul_comm (x j) (sig s a),smul_comm (x j) (sig s b)]
lemma slides (a:Axis): (σ).air ( Ray G m k z ( s.perm a ) (R x))=sig s a • Ray G m k z a x:= by
 unfold Ray; rw [air_p,map_sum, smul_comm (sig s _) ((slotDen k)⁻¹)]; congr 1; rw [Finset.smul_sum]; rw [ ← Equiv.sum_comp s.perm ]; apply Finset.sum_congr rfl; intro j _; rw [ax_v,air_p,ray_top,mul_comm (sig s j),mul_smul,sig_t,smul_comm]
lemma directs (i:G.ColorIndex): cash s m ( Ray G m k z (s.perm a) (R x) i)= sig s a • Ray G m k z a x i:= congr_fun (slides s a) i
lemma hood (i:G.ColorIndex): (Prong (s.perm a) (R x) i (h:=k)).comp ( Taylor.turn s.ortho )= sig s a • Prong a x i:= by
    apply LinearMap.ext; intro X
    change (Taylor.value (Taylor.turn _ X) (s.perm a) (R x)) i=_; rw [Taylor.turn_value,Ortho.inv_move ]; unfold Signed.ortho; simp_rw [Brass.mat_t, EmbeddingLike.apply_eq_iff_eq,ite_smul,zero_smul]; simp; split <;> simp [Prong,Taylor.value]
lemma guide (X:Coord G k): cash s m (Ramp G k (asC G k X) z m)= Ramp G k (asC G k ( X.comp (Taylor.turn s.ortho))) z m:= by
    have he:X∈ Submodule.span ℝ (Samples G k):= by rw [many]; exact Submodule.mem_top
    refine Submodule.span_induction («R»:=ℝ) (p:=fun X _=> cash s m (Ramp G k (asC G k X) z m)= Ramp G k (asC G k ( X.comp (Taylor.turn s.ortho))) z m) ?_ ?_ ?_ ?_ he
    · rintro _ ⟨a,x,c,rfl⟩; obtain ⟨b,rfl⟩:=s.perm.surjective a; obtain ⟨u,rfl⟩:∃ u:E4,x= R u:= ⟨ _,(Ortho.move_inv s.ortho x).symm⟩; rw [ramp_Jrad,directs, hood,map_smul,show Ramp G k ( sig s b • _)=_ from map_smul (Ramp G k) ( ( sig s b:ℝ ):ℂ ) _, Pi.smul_apply, Pi.smul_apply,ramp_Jrad]; rfl
    · rw [map_zero,map_zero, Pi.zero_apply,Pi.zero_apply,map_zero,LinearMap.zero_comp,map_zero,map_zero]; rfl
    · intro f g H K hO hg; simp only [LinearMap.add_comp,map_add,Pi.add_apply,hO,hg]
    intro c i H hx; simp only [LinearMap.smul_comp,map_smul (asC G k),show ∀ X: Witness G k,Ramp G k ( c • X )=(c:ℂ) • Ramp G k X from fun X=>map_smul _ (c:ℂ) X,map_smul, Pi.smul_apply, hx]
abbrev rotatedQ (s:Signed):= changed ( G:=G ) fun _=> Taylor.turn s.ortho
lemma rotated_id (s:Signed): rotatedQ (G:=G) s= Labels.rotated s.ortho⁻¹:= by unfold rotatedQ Labels.rotated; rw [inv_inv]
lemma equivariant (p:Pol G): cash s m ( seed G p z m )= seed G (rotatedQ s p) z m:= by
    induction p using MvPolynomial.induction_on with
    | C a=> rw [rotatedQ,changed,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,sightC]; exact Surf.fixC σ a
    | add i j h k=> simp only [map_add,Pi.add_apply,h,k]
    | mul_X p i hp=> rw [map_mul (rotatedQ s),seed_p,seed_p,show cash s m (bite m G _ _)=_ from Pilot.circle_prod _ _ _,hp, seed_x,show rotatedQ s (MvPolynomial.X i)=_ from Theater.moved_v (fun _=> Taylor.turn s.ortho) i,Vtheta,sampleC,guide]; rfl
end YM.FVA2.Position.OpenAxis
