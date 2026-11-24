import YM.FVA2.Probe
/-!
# Scaling of momentum-scheme panel and regulator comparison. This also characterizes X starting
from the Wilson data *without* knowing momentum-subtracted kernels. Then read coupling test on transports.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.FVA2.Pic
open Function Filter Set Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide -- Label ambiguity
open scoped Topology ContDiff Classical
variable {G:Gauge} (V: Warehouse G) {h:G.Simple} {O: Booked (wings G)} (M:MS_Data G O)
variable (s v t:ℝ){q:ℝ}(R:Booth q V.F)(j k d n:ℕ)
local notation "F"=> V.F
local notation "B"=> wings G
def marked (v:ℝ) : Panel V.F:= ⟨ fun d {_} x=> Elegant.phy V M v x.1 d ⟩
local notation "Ω"=> marked V M
local notation "S"=> BoxOffice.warehouse V
local notation "θ"=> nested V.F h (BoxOffice.warehouse V) -- h implicit never binder include condition use notation.
local notation "Λv"=> turns h V M v
open Fountain ( phys score metric shapes )
lemma readMark (p:Points n)(hp:p∈conf n) : Panel.off (Ω v) d p k=Fountain.phys V M v k p d:= by rw [ sees _ hp ]; rfl
lemma clearMark : clearP (Ω v):= by
   intro d m n p; unfold PayAll.taste; refine ContinuousOn.congr (fun (x:Points m) (hx:x∈ conf m)=> ( shapes V M n v x p hx ).continuousWithinAt ) ?_; intro x hx; exact DFunLike.congr_fun (readMark V M v n d m x hx) p
lemma payMark : (Ω v).lives d=Spring.ms V M v d:= by
    funext k m t; ext1 p; rw [ Panel.newly _ t p k (clearMark V M v), Spring.invoice ]; apply Test.apply_eq; intro x hx; exact DFunLike.congr_fun (readMark V M v k d m x hx) p -- func reduction
lemma freshMark : Fresh (Ω v):= by refine ⟨ clearMark V M v, fun t=>?_⟩; rw [payMark]; exact Spring.vintage_ms ..
variable {n d} (w:Fin n→ BasisIx G d)(x:Polyp n)
-- Ray amount identity.Our Δ shifts in Φ. sign y.
def massW (w:Fin n→BasisIx G d) := ∑ j:Fin n,(w j).size
lemma normed₀ : MS.Port.τ (-(Vane.charge ( Label.h ∘ Fountain.pant w ) Finset.univ:ℤ)) t= ((Verne.factor t (massW w)):ℂ):= by
    unfold factor MS.Port.τ
    have he: Real.exp ( - ( (massW w ):ℝ ) * t ) = Real.exp t ^ ( - ((massW w:ℤ)) ):= by rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, zpow_neg, zpow_natCast ]
    rw [he]; rfl
lemma factors_add  : (∏ j:Fin n,( (factor s (w j).size):ℂ ))= (factor s (massW w):ℂ):= by
    unfold factor massW; push_cast; rw [ ← Complex.exp_sum ]; simp_rw [neg_mul]; rw [Finset.sum_neg_distrib,Finset.sum_mul];
lemma basis_sphere (f:Panel V.F)(k:ℕ): (f.swell s).out d x k ( sameAxis V.F d ∘ w )= (factor s (massW w):ℂ) * f.out d (Panel.shiftP s x) k ( sameAxis V.F d ∘ w ) := by
    rw [ Panel.unfold_scl ]; have he : Δ V.F s d ∘ ( sameAxis V.F d ∘ w )=(fun j:Fin n=> ( (factor s ( w j ).size):ℂ) • ( sameAxis V.F d ∘ w ) j ):= funext fun _=> Δ_basis ..;
    rw [he, MultilinearMap.map_smul_univ, factors_add ]; rfl
lemma rateScale1 (k:ℕ): (Ω v).out d (shiftP s x) k ( sameAxis F d ∘ w )= (factor (-s) (massW w):ℂ) * (Ω (v-s)).out d x k ( sameAxis F d ∘ w ):= by
   change Fountain.phys V M v k ( cZ s x.val ) d _= _ * Fountain.phys V M (v-s) k x.val d _; rw [Fountain.onLit,Fountain.onLit, ← normed₀ ]; let p:=metric x.1; have hm:metric ( cZ s x.val )=(fun i=> Real.exp (-s) • metric x.val i ):= funext fun _=> map_smul ( Theater.out ) _ _; unfold Fountain.score; rw [hm, Waves.tour_time M (Fountain.pant w) (Fountain.metric_conf x.property) k v (-s) Finset.univ ]; rfl
lemma scaled (s:ℝ) : swell ( Ω v ) s = Ω (v-s):= by
    apply Panel.ext; intro d m x; funext k; apply Module.Basis.ext_multilinear (fun j:Fin m=> sameAxis V.F d); intro w; change ( (Ω v).swell s ).out d x k ( sameAxis F d ∘ w )= (Ω (v-s)).out d x k ( sameAxis F d ∘ w ); rw [ basis_sphere, rateScale1 ,← mul_assoc,← Complex.ofReal_mul, factσ ]; simp [factor]
-- Cohort all-η, one detector. MS read test.Need Smooth.Ready and detectable. h Simple.
lemma time_marked (w:Fin n→ BasisIx G d) : Ready (fun y:ℝ=> fun x:Polyp n=>(Ω y).out d x k ( sameAxis V.F d∘ w )):= by simp_rw [show ∀ y:ℝ,∀ x: Polyp n, (Ω y).out d x k ( sameAxis V.F d∘w )= _ from fun y x=> Fountain.onLit V M y w k x.val ]; exact MS.FV2Mod.toured M (fun i=> metric ( i:Polyp n ).val ) (fun i=> Fountain.metric_conf i.property ) (Fountain.pant w) Finset.univ k
include h
def normalize (V:Warehouse G) (M:MS_Data G O)(v:ℝ)(h:G.Simple) : Strat V.F:= ⟨ turns h V M v, fun {_ _} g=> Elegant.family h V M v g ⟩
def L (h:G.Simple): Strat V.F:= normalize V M v h
lemma pulseL : (Pic.L V M v h).pulse:= fun k=> report_st _ ( θ k ) ( Spring.vintage_ms .. ) -- ambiguity
lemma collect : metricT R (((Ω v).flip (Pic.L V M v h)).lives 6)= Elegant.ξ h V M v R := by rw [ turn_book _ _ (clearMark V M v),payMark ]; rfl
lemma realizer : Panel.testable (Ω v) θ R=Elegant.ξ h V M v R:= by unfold testable; rw [payMark ]; rfl
lemma normalized_frame (k:ℕ) : ( ( Ω v ).flip ( Pic.L V M v h ) ).lives k= Elegant.pattern h V M v k:= by rw [ turn_book _ _ ( clearMark V M v ),payMark ]; rfl
-- Raw Wilson PSPace Shot R from bare alignment before mass-independent relation.TrueK and bright. This makes canonical witness on any express height.
open BoxOffice Sail
abbrev X (V:Warehouse G)(h:G.Simple) (M:MS_Data G O)(v:ℝ){q:ℝ}(R: Booth q V.F) := Panel.join (Panel.flip (marked V M v) (Pic.L V M v h)) (Jet.inverse ( Elegant.ξ h V M v R ))
local notation "Xv" v=> Pic.X V h M v R
lemma Xtrue (x:Polyp n) : (Xv v).out d x= Elegant.trueK h V M v R x.val d := rfl
lemma XL (k:ℕ) : ( Xv v ).lives k= Elegant.bright h V M v R k := by rw [X,total_book _ _ (Panel.night _ _ ( clearMark V M v )), normalized_frame ]; rfl
lemma innerX : ( Xv v ).Fresh:= Panel.Fresh.pre _ (Panel.Fresh.matrix _ ( freshMark .. ) ( pulseL V M v ( h:=h ) )) (Jet.lives _)
variable {B0:Booked (wings G)} -- need angular
-- Instead use ALL M orientation and wait characterization.Sel. companion can choose Booked precisely by radial criterion once built.Use ContinuumConcord as El parameter.
structure pass (h:G.Simple) (M:MS_Data G O) (R:Booth q V.F): Prop where
    lens (v:ℝ): Genuine ( Elegant.ξ h V M v R )
    lane (v:ℝ): ( Elegant.ξ h V M v R ) 1=1
    learns (v:ℝ)(d:ℕ)(q:ℕ+)(hq:1<q.val) : Wait atTop (fun i=> renormal ( warehouse V ) q h R i d) ( Elegant.bright h V M v R d )
lemma supplies (M:MS_Data G (ArchTurn.angular B0 V)) (P:Land.Prescription (wings G))(H:Blaze.ExactSpin V P)(HI: Frost.Trusted P)(C:Sail.Concord h V B0 M P H HI R) : pass V h M R:= ⟨ fun i=>(C.light i).1, fun i=>(C.light i).2,C.limit ⟩
-- H=simple gauge.
variable (Sx: pass V h M R)
def tradeT (W:Warehouse G)(h:G.Simple){q:ℝ}(R:Booth q W.F)(C: Panel W.F) : Prop:= ∀ (d:ℕ)(q:ℕ+)(_:1<q.val), Elegant.Wait (l:=atTop) (fun i=> Bend.renormal (warehouse W) q h R i d) ( C.lives d ) -- l implicit?
include Sx
lemma underlying : tradeT V h R ( Xv v ):= by intro d q hq; rw [XL ]; exact Sx.learns v d q hq
-- uniqueness from independent data. system on all x since test smooth and order maps compatible. Already Tags RMS; Input sector. Also market-normalized v.Fr.Th.Vision.
omit Sx
lemma uniqueX (Q W:Panel V.F)(H:Q.clearP)(hq:W.clearP)(hv:tradeT V h R Q)(ht:tradeT V h R W): Q=W:= by apply Panel.chain_real Q W H hq; funext d k m p; ext1 q; let t:=Pert.Position.Section.mk ( «F»:=V.F) m q p; exact tendsto_nhds_unique ( hv d 3 (by decide) k t ) ( ht d 3 (by decide) k t )
include Sx
lemma across (s t:ℝ) : X V h M s R=X V h M t R:= uniqueX V R _ _ (innerX ..|>.1) (innerX ..|>.1) (underlying V M s R Sx) ( underlying V M t R Sx )
lemma payX (v:ℝ)(k:ℕ): Jet.ren ( Elegant.ξ h V M v R ) (( Xv v ).lives k)= ( (Ω v).flip (Pic.L V M v h) ).lives k:= by
   let a:= Elegant.ξ h V M v R; rw [← total_book _ _ (innerX ..|>.1) ]; apply congr_arg ( fun A: Panel V.F=> A.lives k ); rw [Pic.X, Panel.join_step _ _ _ ( Jet.lives _ ) (Sx.lens _).1, headback ( Sx.lens _ ), join_id ]
omit Sx in
lemma nearX (k:ℕ): ( θ k ).announce ( ( Xv v ).lives k ) 0 := by
    rw [XL ]; unfold PositionX.Detector.announce; rw [Verne.float ]; unfold Elegant.bright pattern; rw [ ren_writes ]; obtain hP : ( θ k ).D ∘ predMarket ( turns h V M v k ) ( Spring.ms V M v k )= just (( θ k ).D (pureBank V.F k)):= Elegant.exactD h V M v k; rw [hP]; exact Jet.ren_static ( ( θ k ).D (pureBank V.F k ) ) (Jet.lives _)
lemma modeX : (Xv v).testable θ R=headway:= by
   let U:=Xv v; obtain hh:= Elegant.solves_only ( θ 6 ) (U.lives 6) (innerX V M v R|>.2 6); have ht : Detector.report ( θ 6 ) ( (Xv v).lives 6 )=0:= ( hh.2.2 0 rfl ( nearX V M v R _ ) ).symm; rw [ testable, ht,float,Pic.X,total_book _ _ (Panel.night _ _ (clearMark V M v)), Bend.meter_ren _ _ _ ( Jet.lives _ ), collect ]; exact guarded ( Sx.lens _ )
end YM.FVA2.Pic
