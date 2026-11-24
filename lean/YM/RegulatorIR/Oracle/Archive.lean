import YM.RegulatorIR.Oracle.Hamlet

/-! Anchor assembly and post bills depend on Patch and order. Age/cell
-- constants granted in the surrounding schedule. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {G:Gauge} {X Y A B I V: Type} {α σ Ω Ω' δ δ' l s P:ℝ} {u p q k i j:ℕ} {n t f:Side}

def cabins (P:Patch):Side:=4*P.L
private lemma evenA : Even (4:Side).val:=by norm_num
private lemma evenL (P: Patch) : Even (cabins P).val:=evenA.mul_right _
private def plen (P:Patch):ℝ:= (4:ℝ)*P.L.val
private lemma scaled (P:Patch): (1:ℝ)*(cabins P).val=plen P :=by unfold cabins plen; push_cast;ring
private lemma thick (P:Patch):(P.L.val:ℝ)*(4:Side).val=plen P:=by unfold plen;push_cast;ring
private abbrev GetV (P:Patch)(G:Gauge):=Binding.Book G (cabins P) ⊕ Binding.Book G 4
private def du (P:Patch) (G:Gauge): Deck (plen P) (KFoot G) (GetV P G):= Step.combine (Carto G _ _ (evenL P) (scaled P)) (Carto G _ _ evenA (thick P))
private abbrev MixV (P:Patch) := PertExtension.Orb.OEdge (cabins P)⊕PertExtension.Orb.OEdge 4
private def para (P:Patch): Parade Branchix (MixV P):= unite (posMarch (evenL P)) (posMarch evenA)
private def Tar (P:Patch)(G:Gauge)(k:ℕ):= (Tariff.native P.L.val (by positivity) k).uses (du P G).pos
private def postage (P:Patch)(i k:ℕ)(u:Packet (KFoot G) i):= quota u (Tar P G k).diameter
private lemma cob (P:Patch)(G:Gauge)(i k:ℕ)(u:Packet (KFoot G) i)(h:Bounded u): postage P i k u≠⊤:=boundedC h (K:=Tar P G k) fun _ _=>by unfold Tar Tariff.uses Tariff.native;dsimp only;unfold Tariff.amount; finiteness

variable (P:Patch)(H: KernelChoices)(G:Gauge) (Z:P.Branches H G)
private abbrev menuB := avenue P H 4

def ringQ (P:Patch)(H: KernelChoices)(G:Gauge)(_Z:P.Branches H G)(t:Edge Cover):Orders (KFoot G):= ((rooted (menuB P H) (stemF P 4) t).some.issues (1:ℝ) 0).choose -- Z unused
private def penn (k i j:ℕ): Branchix→ℝ≥0∞
 | .inl v => postage P j k (ringQ P H G Z v i j)
 | .inr v => ∑ m∈Finset.HasAntidiagonal.antidiagonal i, postage P j k (standby (S:=menuB P H) Z v (m.2+2) j)

def archive (P:Patch)(H:KernelChoices)(G:Gauge)(Z:P.Branches H G) (i j k:ℕ):ℝ≥0∞:=∑ x:MixV P, penn P H G Z k i j ((para P).bare x)
private lemma pricingV (k i j:ℕ)(x): penn P H G Z k i j x≠⊤:= by
 cases x
 next v =>exact cob _ G _ _ _ (((rooted (G:=G) (menuB P H) (stemF P 4) v).some.issues 1 0).choose_spec.sized ..)
 next v=> exact ENNReal.sum_ne_top.mpr fun k _=> cob _ G _ _ _ (boosted (S:=menuB P H) Z v |>.sized ..)
lemma archived i j k : archive P H G Z i j k≠⊤:= ENNReal.sum_ne_top.mpr fun _ _=> pricingV P H G Z k i j _

def valor (T:Binding.Scale)(i:ℕ):= 1+∑ k∈Finset.range (i+1), ‖biases T k‖ₑ
lemma valor_f (T:Binding.Scale) i: valor T i≠⊤:=by unfold valor; exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.sum_ne_top.mpr fun _ _=>by finiteness⟩
section earn
variable {T:Branchix→Orders (KFoot G)} {S:Binding.Scale}
include Z
omit Z in
private lemma tissue (p:Prim.Sphere (avenue P H n) (stemF P n) S T):Prim.Sphere (menuB P H) (stemF P 4) S T:=by
 have hv:= Older.neverP (G:=G) (avenue P H n) (menuB P H) rfl rfl S
 intro x; rw [show prism (menuB P H) (stemF P 4) S x=_ from congr_fun hv.symm x]; exact p x
private lemma tout (p:Prim.Sphere (menuB P H) (stemF P 4) S T) k i j a : postage P j k (T a i j)≤ valor S i * penn P H G Z k i j a:=by
 cases a with
 | inl a=>
    unfold penn
    have hp : T (.inl a)=ringQ P H G Z a:= (p (.inl a)).unique (((rooted (menuB P H) (stemF P 4) a).some.issues (1:ℝ) 0).choose_spec)
    rw [hp]; exact le_mul_of_one_le_left (by simp) le_self_add
 | inr a=>
    by_cases ht:i=0
    · subst i; rw [(p (.inr a)).awake]; exact (quota_zero _).trans_le bot_le
    rw [milk (S:=menuB P H) Z S (x:=a) (W:=T (.inr a)) (p (.inr a)) i (Nat.pos_of_ne_zero ht),laterBias,Finset.sum_apply];
    unfold postage; apply le_trans (quota_sum _ _ _);unfold penn;rw [Finset.mul_sum]; refine sum_le_sum fun m hm=>?_
    have he: ‖biases S m.1‖ₑ ≤ valor S i := by
       apply le_trans _ le_add_self
       refine Finset.single_le_sum (f:=fun k=> ‖biases S k‖ₑ) (fun _ _=>zero_le) (Finset.mem_range.mpr ?_); have hv := mem_antidiagonal.mp hm; omega
    dsimp only [Pi.smul_apply]; exact (quota_times _ _ _).trans_le (mul_le_mul_left he _)
private lemma assets (p:Prim.Sphere (avenue P H n) (stemF P n) S T)(i j:ℕ): localQ (Tar P G k) (many T i j) (valor S i *archive P H G Z i j k):=by
 have hv:= tissue P H G p
 have hp:= cosmos (menuB P H) (stemF P 4) S Z (evenL P) (scaled P) evenA (thick P) hv
 refine local_mono (Tar P G k) (T:=massive (fun a=> T a i j)) (axi_cost (du P G) (para P) (Tar P G k) _ (hp.paves i j) (capableM (du P G) (u:=k) (l:=(P.L.val:ℝ)) (by positivity))) ?_
 unfold archive; rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _=> tout P H G Z hv k _ _ _

omit Z
private lemma seat_mul (l b:ℝ)(x:Edge Cover) : seat (l*b) x=l • seat b x:=by
 let he z : Motion.slide (l*b) z=l • Motion.slide b z:= by ext i;simp; ring
 unfold seat glint; rw [smul_add,he,he,smul_comm l]
def peak_o (G:Gauge)(l b:ℝ): KFoot G→Room:= Sum.elim (fm G l) (fm G b)
private lemma peakP {p:KFoot G}{l r:ℝ}(h:r=l*P.L.val):peak_o G l r p=l • (du P G).pos p:=by
 cases p with
 | inl x=> change seat l x.1=l • seat 1 x.1;simpa using! seat_mul l 1 x.1
 | inr x=>exact h ▸ (seat_mul l _ x.1)
private lemma tarQ (i j:Tariff X)(h:i.road=j.road): i=j:=by cases i;cases j;simp only [Tariff.mk.injEq];exact h
include Z
lemma financed (p:Prim.Sphere (avenue P H n) (stemF P n) S T) (h:0<l)(hv:s=l*P.L.val)(ht:0<s)(i j:ℕ): localQ ((Tariff.native s ht k).uses (peak_o G l s)) (many T i j) (valor S i*archive P H G Z i j k):=by
 have hp:(Tariff.native s ht k).uses (peak_o G l s)= Tar P G k:=by
    apply tarQ; ext1 x;ext1 y; change Tariff.amount s k (dist (peak_o G _ _ x) (peak_o G _ _ y)) = _;rw [peakP P G hv,peakP P G hv,dist_smul₀,Real.norm_of_nonneg h.le]; unfold Tariff.amount; rw [hv,mul_div_mul_left _ _ h.ne'];rfl
 rw [hp]; exact assets P H G Z p i j
end earn
end YM.RegulatorIR.Oracle
