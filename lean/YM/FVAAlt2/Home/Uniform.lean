import YM.FVAAlt2.Home.Geometry
/-! Uniform compact estimate and estimates on real separated profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Profiles
open Function Finset Filter Topology Lattice
open Set Metric MeasureTheory
open MS MS.Koszul MS.Menus MS.Book MS.Theater MS.Tone MS.Vista MS.Fleet MS.High MS.Tide MS.Orbit MS.Rake
open Extraction
open Pert.Orb PertExtension PertExtension.LatticePT
open Real
open scoped Topology BigOperators ContDiff
variable {d:ℕ}{q:ℕ+}{n:ℕ}{K:Set (Points d)}
local notation "u"=> Locus q K
local notation "V"=> LatticePT.Native q n
variable (μ:ℝ)
local notation "Φ"=> posterT q K μ
set_option quotPrecheck false
local notation "γ"=> (Φ).profile
local notation "X"=> stopT q K

set_option quotPrecheck false

lemma poster_width : Vista.width (Φ).side (Φ).head:= by -- replace header
 apply centered_size; intro i; rw [visit_one]; change Lattice.lift i.u= _; simp_rw [show (Φ).head i= Lattice.lift i.u from rfl,wrap_lift]
lemma poster_clear : Clearance (Φ).side (Φ).head:= by
 intro i v; apply remote; · have hs := center_bound i.inside|>.1; change (dimT (Φ).side i).val ≤ 8*pdist (wrap (dimT (Φ).side i) (Lattice.lift i.u)); rw [visit_one, wrap_lift]; exact hs
 have hs := center_bound i.inside|>.2; change 4*pdist (wrap (dimT (Φ).side i) (Lattice.lift i.u)) ≤ (dimT (Φ).side i).val; rw [visit_one,wrap_lift]; exact hs

-- compact of *separated points*, sup vs Hilbert, no implicit x=0 padding.
def realize (x:Points d)(i:Fin d):QP:= out (x i)
@[fun_prop] lemma realize_s : Continuous (realize (d:=d)):= continuous_pi (fun i=> out.toLinearMap.toContinuousLinearMap.continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin d=> E4) i))
lemma realize_one {x:Points d}(hx:x∈ YM.conf d): Function.Injective (realize x):= fun i j he=> hx (out.injective he)

lemma profileW (hK:IsCompact K): Profile (Φ).profile (Φ).off:= by
 intro w
 let f(x:Points d):= realize x w
 have hf : Continuous f:= ( continuous_apply w ).comp ( realize_s ); obtain ⟨r,H⟩:= (hK.image hf.norm).bddAbove
 set a:=1+max 0 r
 have ha:0<a:=by unfold a; linarith [le_max_left 0 r]
 refine ⟨a,ha,fun i=>?_⟩
 have hp : ‖exp (-(γ).θ i) • embed ((Φ).off w i)‖≤ a:=by
    apply le_trans (b:=r) _ (by unfold a; linarith [le_max_right 0 r]); change ‖Dial.testP Φ i w‖≤_; rw [framesS]; apply H; exact ⟨ Grid.sample q i.level i.x,i.inK,rfl⟩
 rw [norm_smul_of_nonneg (exp_pos _|>.le),exp_neg,←div_eq_inv_mul] at hp; exact ( div_le_iff₀ (exp_pos ((Φ).profile.θ i)) ).mp hp

lemma poster_mesh (hK:IsCompact K)(h:K⊆conf d): Mesh (Φ).profile (info (Φ).off):= by
 apply Dial.unpose (v:=μ); intro i j he; let c(x:Points d):= ‖realize x i-realize x j‖
 have hc : Continuous c:= by unfold c; fun_prop
 obtain ⟨m,hm⟩:= (hK.image hc).bddAbove
 have hz:∃ a:ℝ,0<a∧∀ x∈K,a≤ c x:= by
   cases Set.eq_empty_or_nonempty K with
   | inl h=> exact ⟨1,zero_lt_one,fun x he=> (Set.notMem_empty x ( h ▸ he )).elim⟩
   | inr hx=> obtain ⟨x,hx,ht⟩:= hK.exists_isMinOn hx hc.continuousOn; exact ⟨ c x,norm_pos_iff.mpr (sub_ne_zero.mpr ((realize_one (h hx)).ne he)),ht⟩
 have hv(x:Locus q K): ‖(Tide.lifted (Φ).profile (Φ).off i-Tide.lifted (Φ).profile (Φ).off j) x‖= c (Grid.sample q x.level x.x):=by change ‖Dial.testP Φ _ _-Dial.testP Φ _ _‖=_; rw [framesS]; rfl
 obtain ⟨a,ha,h⟩:=hz; set b:=1+max 0 m; have hb:0<b:=by unfold b; linarith [le_max_left 0 m]
 refine ⟨⟨ b,hb,fun x=>?_⟩,⟨ a,ha,fun x=>?_⟩⟩ <;> rw [hv x] <;> simp only [Rake.Geo.roots,frameF, Pi.zero_apply,exp_zero, mul_one]
 · exact le_trans (hm ( Set.mem_image_of_mem c x.inK )) (by unfold b; linarith [le_max_right 0 m])
 exact h _ x.inK
lemma books (hq:1<q.val)(hK:IsCompact K)(h:K⊆conf d): Dial.Uses Φ X μ:= ⟨profileW μ hK,poster_mesh μ hK h,rfl_t, Tendsto.comp (g:=Θ q) (grows hq) tendsto_comap, fun x=> Filter.Eventually.filter_mono (le_refl _) ((tendsto_comap (f:=Locus.level)).eventually (all_ss hq x)), poster_clear _,poster_width _ ⟩
 where rfl_t i:= rfl -- Lean infer?

variable {G:Gauge}{L:Labels.Frames G} {H:Source.Hol G}{B: MS.Local.Physical.Deck G}{M:MS.Land.Booked B}
variable (D: Precision.ChartRatio G)(R:Lobby.Registry L H)(S:MS.Land.MS_Data G M)(P:MS.Land.Prescription B)(p:Fin d→ Rake.Label B)

-- unfolded pixel point price: measured step heading & log δ, density power of ε. uses committee estimate Profile BEFORE any position frame normalization.
variable (q n)
def pixelT (q:ℕ+) (n k:ℕ)(p:Fin d→ Rake.Label B)(x:Grid.offsets q d n)(o:Native q n):ℂ:= PowerSeries.coeff k (Lobby.newEra D R P (μ-Θ q n) p (address q n x o) (epsilon q n))
-- chart trajectory ratio D: true chosen
variable {q n}
lemma castW (w:Locus q K)(k:ℕ): Lobby.evaluateR D R P p Φ μ k w= pixelT (d:=d) μ D R P q w.level k p w.x w.u:=by
 unfold pixelT Lobby.evaluateR Lobby.situated;
 rw [ billingS ]; change PowerSeries.coeff k (Lobby.newEra D R P (μ-Θ q w.level) p (fun i=> wrap (dimT (Φ).side w) ((Φ).head w+(Φ).off i w)) (epsilon q w.level))= _; rw [visit_one];
 apply congr_arg; apply congr_arg (fun x=> Lobby.newEra D R P _ p x _); funext a; rw [map_add]; change _=w.x a + w.u; change wrap _ (Lattice.lift _)+ wrap _ (Lattice.lift _) = _; rw [wrap_lift,wrap_lift,add_comm]

lemma reception (h:Precision.LocalRatio D) (hk:MS.Land.TaylorOKPl S (Lobby.Table R B) P)(hG:G.Simple) (hK:IsCompact K)(hu:K⊆conf d)(hq:1<q.val)(n:ℕ):
    ∃ C:ℝ,0<C∧∀ᶠ k in atTop,∀ (x:Grid.offsets q d k), Grid.sample q k x∈K→∀ a∈ origins q k,
      ‖pixelT (d:=d) μ D R P q k n p x a - Dial.tour S p μ (realize (Grid.sample q k x)) Finset.univ n‖ ≤ C* Real.exp (-mildG* Θ q k):= by
 obtain ⟨ -,C,hC,H ⟩:=( Lobby.pays_all D R P p S h (books μ hq hK hu) hG hk).pay n
 refine ⟨ C,hC,(files H).mono ?_⟩; intro k h x hx a ha; let i:u:= ⟨ k,x,hx,a,ha⟩; obtain hu:= h i rfl; rw [Pi.sub_apply,framesS,castW] at hu; exact hu
end YM.FVAAlt2.Home.Profiles
