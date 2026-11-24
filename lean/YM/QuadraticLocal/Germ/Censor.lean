import YM.QuadraticLocal.Germ.Stock
import YM.RemainderComparison.Solos.Huts
/-!
# Polishing the carried nominal test functions on closed masks

 No change *inside* or at boundary (also equal as germs at all equality flags),
 extends each preserving Kern rules. For any stable restriction; reuse Huts
 (extend to complex, any Lens on budget). Global clear handled cautiously; all
 U extension must still be pure. When cutting addresses, retain all masked
 germs of labels kept and equality of masked values of any ghost omitted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Affinity.Polish
open Function Filter Finset MeasureTheory RemainderComparison
open Marker Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι:Type*} {θ:Type} [DecidableEq θ] {α:Type*} {n c:Side}{G:Gauge}
variable (P:BudgetPoint)(S:Support c)(U V:Config G c)
variable {X:θ→Support n}{o:θ→ Site n}
variable {Y:θ→Type*}[∀ i,AddCommGroup (Y i)]{𝕜:Type}[RCLike 𝕜][NormedAlgebra 𝕜 ℂ][∀ i,Module 𝕜 (Y i)]
variable (A:∀ i,Set (Y i))(K:∀ i,Submodule 𝕜 (Y i))
variable (D : (α→ℂ)→Prop)
open RemainderComparison.Solos (roomier usual)
variable (Φ:α→ Config G c→ℂ)
def promise := interior {v| D fun i=> Φ i v}
def lyric (x:α):Config G c→ℂ := Set.indicator (promise D Φ) (Φ x)
local notation "X"=> promise D Φ
variable (hv:∀ x,P.Regular S (Φ x)) (u:α)
include hv
lemma promise_reads (h: Agrees S U V) : U∈ X ↔ V∈ X :=by
    have hv x y (h:Agrees S x y) : (fun u=> Φ u x)=(fun u=>Φ u y):= funext fun u=> (hv u).sites x y h
    let f v:= D fun i=> Φ i v; have hh (x y)(h:Agrees S x y): f x=f y:= congr_arg D (hv _ _ h)
    simp_rw [promise,mem_interior_iff_mem_nhds]; exact ⟨roomier S U V f hh h,roomier S V U f hh fun e he hk=> (h e he hk).symm⟩
lemma promise_halos (k:Site c→ G.El) : Lattice.gauge k U∈ X ↔ U∈ X:=by
    have hv k U: (fun u=> Φ u (Lattice.gauge k U))=(fun u=> Φ u U):= funext fun u=> (hv u).symmetry k U
    let f v:= D fun i=> Φ i v; have hh(k U) : f (Lattice.gauge k U)= f U:= congr_arg D (hv k U)
    simp_rw [promise,mem_interior_iff_mem_nhds]; have he : Lattice.gauge k⁻¹ (Lattice.gauge k U)=U:=by ext; simp [Lattice.gauge,mul_assoc]
    exact ⟨fun H:∀ᶠ x in 𝓝 _, f x=> he ▸ (usual (Lattice.gauge k U) f k⁻¹ hh H),usual U f k hh⟩
omit hv
-- Family in linear basis.Mode extraction after
lemma growth (x:Config G c) (hd:D (fun _=>0)): D fun b=> lyric D Φ b x:=by
    unfold lyric; by_cases h:x∈ X
    · simp_rw [Set.indicator_of_mem h]; exact (show x ∈ {v| D fun i=> Φ i v} from interior_subset h)
    simp_rw [Set.indicator_of_notMem h]; exact hd
variable (h : ∀ U,Healthy P.threshold S U→∀ᶠ z in 𝓝 U,D fun i=> Φ i z)
include h
lemma sung (hp:Healthy P.threshold S U): lyric D Φ u=ᶠ[𝓝 U] Φ u:= (show ∀ᶠ x in 𝓝 U,x∈ X from isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (show {v| D fun i=> Φ i v} ∈ 𝓝 U from h U hp))).mono fun _ hi=>Set.indicator_of_mem hi _
include hv
lemma epode : P.Regular S (lyric D Φ u):=by
    have hh(U:Config G c)(H:Healthy P.threshold S U) : Push.Local.Chart P.order (lyric D Φ u) U:=by
       apply ContDiffAt.congr_of_eventuallyEq (f:= Φ u ∘ increment U) (hv u|>.smooth U H); apply (sung P S U D Φ u h H).comp_tendsto (by simpa only [Work.G07.at_zero_increment] using! (show Continuous (increment U) from by unfold increment; fun_prop).tendsto 0)
    refine ⟨?_, ((hv u).borel.indicator isOpen_interior.measurableSet), ?_,hh,fun U H A l hl=> Next.Foundations.left_has _ hl (hh U H)⟩ -- finder
    · intro U V h; unfold lyric Set.indicator; simp_rw [promise_reads P S U V D Φ hv h]; rw [(hv u).sites U V h]
    · intro k U; unfold lyric Set.indicator; simp_rw [promise_halos P S U D Φ hv]; rw [(hv u).symmetry k U]
omit hv
lemma poet {B:ℝ} {o:Site c} (hh:P.supBounds o S (Φ u) B) : P.supBounds o S (lyric D Φ u) B:=by
    refine ⟨hh.1,fun U hu l hl hf=> ?_⟩; rw [(UVNext.PricedKernels.left_congr (sung P S U D Φ u h hu) l).self_of_nhds]; exact hh.2 U hu l hl hf
omit h
-- if Clear all links then announce geometry here.
local notation "Lx"=> Wallet A
variable {Q:BudgetPoint}{B:ℕ} {J:Census θ} {v γ σ:ℝ}
variable (L:Lamps (Wallet A) ι G Q o J)(Loc:θ→Support n)
structure Static : Prop where
    honor (i:ι)(U:Config G n): Healthy Q.threshold (L.ground i) U → ∀ᶠ x in 𝓝 U,Attn K A (L.mode i).val (fun t=> L.nominal t i x)
    fare (i:ι) (U:Config G n) (t:Wallet A) : L.light t i U≠0→ ∀ v∈(L.mode i).val, Loc v⊆ L.ground i
variable (hl:Static A K L Loc)
def Apt (i:ι):Prop:= ∀ v∈(L.mode i).val, Loc v⊆L.ground i
local notation "P'"=> {x// Apt A L Loc x}
include hl in
private lemma honored (i) (hv:L.clear i)(Z:Config G n): Attn K A (L.mode i).val (fun t=>L.nominal t i Z):= by
    have he:= hl.honor i 1 (Next.Foundations.one_healthy _ _ Q.threshold_pos.le); simp_rw [fun t : Wallet A=> L.pure t i Z hv]; exact he.self_of_nhds
set_option quotPrecheck false
local notation "Ψ"=> Attn K A
private def up (i) (t:Wallet A):= if L.clear i then L.nominal t i else lyric (Attn K A (L.mode i).val) (fun t=>L.nominal t i) t
def chamber : Lamps (Wallet A) (Subtype (Apt A L Loc)) G Q o J where
    mode i := L.mode i.val
    live i:= L.live i.val
    address i:= L.address i.val
    roots i:= L.roots i.val
    nominal t i:= up A K L i.val t
    legal t i:= by unfold up; split; exact L.legal t _; exact epode _ _ _ _ (fun i' => L.legal i' _) _ (hl.honor _)
    clear i:= L.clear i.val
    pure t i U h:=by rw [up,if_pos h]; exact L.pure t i.val U h
local notation "F'"=> chamber A K L Loc hl
lemma tenancy : Taut Loc A K F':= by
    refine ⟨fun i=>i.prop, fun i U=> ?_⟩
    change Ψ (L.mode i.val).val (fun t=> up A K L i.val t U); unfold up; split; next h=> exact honored A K L Loc hl i.val h U
    next=> exact growth _ _ U Attn.silent
lemma bevel (i:Subtype (Apt A L Loc)) (t:Wallet A) (U:Config G n): (F').light t i U=L.light t i.val U:=by
    unfold Lamps.light; dsimp only [chamber,Lamps.ground]; unfold up; split_ifs with ht; first | rfl | skip
    next =>
       by_cases hu: Healthy Q.threshold (L.address i.val).support U
       · rw [masked_eq _ _ _ _ hu,masked_eq _ _ _ _ hu]; exact (sung _ _ U _ _ t (hl.honor _) hu).self_of_nhds
       rw [masked_ne _ _ _ _ hu,masked_ne _ _ _ _ hu]
variable {w:θ→ℝ} (hw:∀v,0<w v)
lemma costs (h:L.Paid w B γ v) : (F').Paid w B γ v:=by
    obtain ⟨f,hf,hp,hH⟩:= h.budget
    refine ⟨(fun i=> f i.val),fun i=> hf _, fun i t u hu=> ?_,fun i=> ?_⟩
    · unfold chamber; dsimp only; unfold up; split; exact hp i.val t u hu; exact poet _ _ _ _ t (hl.honor _) (hp _ t u hu)
    exact Push.AbsoluteSums.budget_pull _ (show Injective (Subtype.val («p»:=Apt A L Loc)) from Subtype.val_injective) (hH i)
lemma stems (t:Wallet A)(U:Config G n): (F').log t U=L.log t U:=by
    unfold Lamps.log; simp_rw [Lamps.frame,bevel]; dsimp only [chamber]; refine Function.Injective.tsum_eq Subtype.val_injective (?_ : Function.support (fun i=> Poly.send (L.mode i) (L.light t i U)) ⊆ Set.range (Subtype.val : P'→ι))
    intro i hi; have ht : L.light t i U≠0:= fun hv=> hi (by simp [hv]); exact ⟨⟨i,hl.fare _ _ _ ht⟩,rfl⟩ -- function support
end YM.QuadraticLocal.Affinity.Polish
