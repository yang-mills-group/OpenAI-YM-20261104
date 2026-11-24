import YM.FVAAlt2.Home.Amber
/-!
# Full-array regulator limit on marked spectrum compatible with Plan
Launch of the SAME finite frame on that Plan and the rule used in setting physical
normalizations. Verifies pivot leading agreement with the analytic test reference.
It does not bound conversion matrices separately, nor after any later couplings.
Keep weighting, choice of sector lifts and test scope exact throughout. REAL profile
transform as in Plan.begins: inputs are all complex labels (by C linear extension of
these real fields of guaranteed basis), `Position` arity uses `Physical.Profile`; the test
is taken in the real scalar part only for determining this Y.real data. Because
connection is real and real columns, this is sufficient for arbitrary real-valued profiles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Report
open Function Set Filter Finset Topology Lattice
open Precision Extra.FD Maxwell Labels Extraction
open FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open MS MS.Local.Physical MS.Koszul MS.Menus MS.Book MS.Plane MS.Theater MS.Land
open MeasureTheory
open RG10.Position (Plan Spur Loft Deck)
open PowerSeries (C coeff constantCoeff)
open Profiles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {G:Gauge}{L:Frames G}{B:MS.Local.Physical.Deck G}{M:Booked B}{H:Source.Hol G}
variable {d r:ℕ}
variable (P:Plan L)(D: ChartRatio G){q:ℕ+} (m:ℕ) (μ:ℝ)
set_option linter.unusedSectionVars false
local notation "F"=> Glyph B d
local notation "Y"=> RG10.Position.Deck L d
local notation "pXC"=> PertExtension.Physical.Profile
local notation "PSc"=> PowerSeries ℂ
local notation "PS"=> PowerSeries ℝ
local notation "μT"=> μ- Profiles.Θ q m
private abbrev CostU (p:Datum F): Fin p.1.n → Rake.Label B := fun i=> Lobby.owner (p.2 i)

variable (S:MS.Land.MS_Data G M)
def currentM (p: Datum F): PS:= forecast S (CostU p) μ (dim_report p)
def science (L:Frames G)(d:ℕ): Datum ( RG10.Position.Deck L d ) →PS:= mix (currentM μ S) ((dout L B d).map C)

lemma beacon {L':Labels.Frames G} (K: MS.Land.Prescription B)(hq:1<q.val)(w:Datum F)(R:Lobby.Registry L' H)(hD:LocalRatio D)(hg:G.Simple)(hk:TaylorOKPl S (Lobby.Table R B) K): AlignSeries atTop (fun m=> takeReal (genus R D q m μ K w)) (currentM μ S w):=by
 obtain ⟨⟨i,f⟩,p⟩:=w; apply goes D R S K (Lobby.owner ∘ p) μ hD hq hg hk (Complex.re ∘ (fun v=> f v)) f.hasCompactSupport f.tsupport_subset (fun i hi=> subset_closure (fun H=> hi (show _= (0:ℝ) from by unfold Function.comp; dsimp only; rw [H];rfl))) (Complex.continuous_re.comp f.continuous) -- inside support
lemma move_limit {W Z I:Type}[Fintype W][Fintype Z]{l:Filter I} (D: Matrix Z W PS) {A: Datum W→I→PS}{A': Datum W→PS}(h:∀v:Datum W, AlignSeries l (A v) (A' v))(p:Datum Z): AlignSeries l (fun j=> mix (fun v=>A v j) D p) (mix A' D p):=by unfold mix; exact AlignSeries.sum (I:=Fin p.1.n→W) (fun j i=>_) (fun i=>_) fun i=> (h _).mul (AlignSeries.const _)

section
local notation "Dk"=> seats P.liftOff P.certified
variable (q)
local notation "T"=> nativeR P
variable {M:Booked (seats P.liftOff P.certified)}(S:MS.Land.MS_Data G M) (X:MS.Land.Prescription (seats P.liftOff P.certified))
def employed (d:ℕ) : Datum (RG10.Position.Deck L d)→PS:= PertExtension.Position.insert _ _ (PowerSeries.subst (revise X.team μT) ∘ P.begins q m d) (frameO L Dk q m μ X d)
lemma element (hD:LocalRatio D): employed (m:=m) P q μ X d=mix (takeReal ∘ genus T D q m μ X) ((dout L Dk d).map C):=by -- X order inspect
  suffices H: into ∘ employed P q m μ X d= into ∘ mix (takeReal ∘ genus T D q m μ X) ((dout L Dk d).map C) by exact funext fun i=> Profiles.rein (congr_fun H i)
  unfold employed; rw [mixSame,mixPap,mixPap,← θout L, show into ∘ (takeReal ∘ genus T D q m μ X)= genus T D q m μ (d:=d) X from funext fun i=> actualBill D T _ _ μ _ q m]; rw [←authentic D q m μ (K:=X) hD,mixSame]


theorem measured (p:Datum (RG10.Position.Deck L d)) (hD:LocalRatio D)(hg:G.Simple)(hx:TaylorOKPl S (Lobby.Table T Dk) X)(hq:1<q.val): AlignSeries atTop (fun m=> employed (m:=m) P q μ X d p) (science (B:=seats P.liftOff P.certified) μ S L d p):= by
 simp_rw [element (D:=D) (hD:=hD)]; apply move_limit _ (h:=fun v=> beacon D μ S X hq v T hD hg hx) -- order check
end

-- identity on engineering dimension leading, all Slot.Profile.Tests.f.real.
variable (L)
def wickB {W:Type}(b:Module.Basis W ℂ (Table.Field (freeTable L) d))(p: Fin r→W)(x:Points r):= Wick.moment G x (fun i=> writes L d ( b (p i) ))
def wickY {W:Type}(b:Module.Basis W ℂ (Table.Field (freeTable L) d))(p:Datum W):= ∫ x:Points p.fst.n,p.fst.test x* wickB L b p.snd x
lemma readable {W:Type}(b:Module.Basis W ℂ (Table.Field (freeTable L) d))(p:Datum W): Integrable (fun x:Points p.fst.n=> p.fst.test x* wickB L b p.snd x):= p.fst.test.smearing (fun x hx=> (Wick.moment_smooth (G:=G) _ hx).continuousAt.continuousWithinAt)
lemma wick_m(i:Datum F){x:Points i.fst.n}(hx:x∈ conf _): (wickB L (mast B d L) i.snd x).im=0 := by
 apply Complex.conj_eq_iff_im.mp; unfold wickB; change star (Wick.moment G x _)=_; rw [← wick_bar hx ]; apply congr_arg; funext j; rw [← writes_bar (h:=table_spin L)]; exact congrArg _ (peg_bar (L:=L) (i.snd j))
lemma dawnM (p: Datum ( Glyph B d )): constantCoeff (currentM μ S p)=( wickY L (mast B d L) p ).re := by
 rw [currentM, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,forecast,PowerSeries.coeff_mk, wickY]; refine Eq.trans ?_ (integral_re (readable L (mast B d L) p)); apply integral_congr_ae; filter_upwards with x
 by_cases h:x∈ YM.conf _;
 · change dim_report _ _ * _ = Complex.re (_ * wickB L (mast B d L) _ x); unfold area realize; rw [ Dial.highest_zero S μ x (CostU p) h,Complex.mul_re, wick_m L p h,mul_zero,sub_zero ]; congr 2; -- need eq of Wick and coordinate
   change Wick.moment G x _=Wick.moment G x _; apply congr_arg; funext j; rw [show mast B d L _= _ from owned (L:=L) (p.snd j),RG10.Position.writes_higher, pegK_owns ]; rfl
 change dim_report p x * _ = Complex.re (p.1.test x * _); simp_rw [dim_report,Function.comp_apply, p.fst.test.vanishes h]; simp
lemma canopy : (mix (wickY L (mast B d L)) (Φout L B d))=wickY L ( RG10.Position.deck L d ):=by
   funext p; let A:=Fin p.1.n; let T:=p.1.test; let x:=p.snd
   let c(i:A→Glyph B d):=∏ j:A, Ωb L B ( x j ) ( i j ); let f:=wickB (r:=p.1.n) L (mast B d L); let g:=wickB L (RG10.Position.deck L d) x
   have he(y:Points p.1.n) : g y= ∑ x:A→F,f x y * c x:= by
      unfold g wickB;
      rw [funext (fun i:A=> show writes L d _ = ∑ k:Glyph B d, Ωb L B (x i) k • writes L d (mast B d L k) from ?_), MultilinearMap.map_sum ]; swap; · rw [← tally_b L B ( x i ),map_sum]; simp_rw [map_smul]
      exact sum_congr rfl fun i _=> (MultilinearMap.map_smul_univ ..).trans (mul_comm ..)
   change _ = ∫ x, T x*g x; simp_rw [he,Finset.mul_sum, ← mul_assoc ]; rw [MeasureTheory.integral_finsetSum];
   · unfold mix; apply sum_congr rfl; intro i _; rw [ integral_mul_const ]; rfl
   intro i _; exact (readable L (mast B d L) ⟨p.1,i⟩).mul_const _
lemma freeσ(p:Datum Y): Physical.free (L:=Maxwell.standard L) (RG10.Position.deck L d) p= (wickY L ( RG10.Position.deck L d ) p).re:= by unfold Physical.free Physical.reading Physical.readingC Test.applyTo; change Complex.re (∫ x:Points p.fst.n,p.fst.test x*(freeTable L).useAt (freeTable L) (1•x) (fun i=>⟨d,(RG10.Position.deck L d) (p.snd i) ⟩))=_; simp_rw [one_smul, writes_eval]; rfl
theorem physics (p:Datum Y) : constantCoeff (science μ S L d p)= Physical.free (L:=Maxwell.standard L) (RG10.Position.deck L d) p:= by
 rw [freeσ L, ← canopy L (B:=B)]; unfold science mix; rw [Complex.re_sum,map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_mul,dawnM L μ S]; -- order
 change _=( _ * ∏ j, Φout L B d (p.snd j) (i j) :ℂ ).re; rw [map_prod]; simp_rw [Matrix.map_apply,PowerSeries.constantCoeff_C];
 rw [show ∏ j, Φout L B d (p.snd j) (i j)=(↑(∏ j,dout L B d (p.snd j) (i j)):ℂ) from ?_]; swap; · push_cast; simp_rw [dout_at]; rfl -- uses simplification dout_at
 simp only [Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero]
end YM.FVAAlt2.Home.Report
