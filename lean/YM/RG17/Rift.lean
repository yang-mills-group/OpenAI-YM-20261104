import YM.RG17.Quartz
import YM.UVNext.COUPLING_RESET.Probe
/-! Dual deployment. conditional ledger
 independent series ports not defined by this ratio. No use of physical
 all flag Taylor approximation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}{s:Extraction.Sequence}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "V"=> role R.family
variable (m Y:ℝ→ℕ)(x:Points 2)(i:Axis) (p:ℕ)
local notation "K"=> (Fin 2)
local notation "A"=> (fun _:Fin 2=> (4:ℕ))
local notation "T"=> interval D s
variable (w:podium R) (q v:ℝ→ℝ)
abbrev punchDebt (L:Layout F)(w:podium R) (q:ℝ→ℝ)(f: K → «Cover»)(r:ℝ)(j:ℕ×ℕ) (x k:ℕ) (z:R.family.label 0): Prop := MirrorDuty R (fun _:Fin 2=> 4) r j.1 j.2 (wrap (R.family.side (wheel C r) j.2) ∘ f) (fun i=>atRef L 4 r j (w r i)) (q r/2) x k z
structure Rift (Z:Ledger L)(s:Extraction.Sequence)(D:Lenses.Mantle F B)(x:Points 2)(i:Axis) where
    plan : Calendar17 R Z s D x i
    X : ℝ→ℕ
    pace : Height R.family.S home OPE.run X (1/2)
    measure : ∀ᶠ r in interval D s, ∀ᶠ j in L.lens,
      (∃ y:R.family.label 0,duty R L plan.m plan.Y plan.wage plan.q plan.v (baseRail R.family x r) y r j ∧ punchDebt R L plan.wage plan.q (baseRail R.family x r) r j (X r) (plan.m r) y) ∧
      (∃ y:R.family.label 0,duty R L plan.m plan.Y plan.wage plan.q plan.v (nextRail R.family x 0 i r) y r j ∧ punchDebt R L plan.wage plan.q (nextRail R.family x 0 i r) r j (X r) (plan.m r) y)
variable (h:Stands L D s)
include h Z W fx
lemma rifting17 (hp:x∈generic 2): Nonempty (Rift R Z s D x i):=by
    obtain ⟨m,hm⟩:= leasable R Z fx; obtain ⟨Y,hY⟩:= found ageLarge (R.family.path.levels.fits.mesh) (by norm_num : (0:ℝ) ≤ 1/2)
    obtain ⟨j,w,H'⟩:= grantedWays R Z fx (fun _=>4) (blue R.family i) W h
    obtain ⟨X,hX,q,v,hq,hv,hV⟩:=assuresMirrors R Z fx W (0:Fin 2) (fun _=>4) j Y m h hm hY; have hl:T ≤ home:= (homes D).comp s.cofinal
    let E(r:ℝ)(f: K → «Cover»)(p:ℕ×ℕ)(y:R.family.label 0):Prop:= MirrorDuty R A r p.1 p.2 (wrap (R.family.side (wheel R.family r) p.2) ∘ f) (fun j=>atRef L 4 r p (w r j)) (q r/2) (X r) (m r) y
    have hs : ∀ᶠ r in interval D s,∀ᶠ p in L.lens,(∃ y,duty R L m Y w q v (baseRail C x r) y r p ∧ E r (baseRail C x r) p y)∧(∃ z,duty R L m Y w q v (nextRail C x 0 i r) z r p∧E r (nextRail C x 0 i r) p z):=by
       filter_upwards [H',hV x (baseRail R.family x) hp ((reachesBase Z fx x).mono_left hl),hV x (nextRail R.family x 0 i) hp ((reachesNext Z fx x 0 i).mono_left hl)] with r hh hu ht
       filter_upwards [hu,ht] with p hu ht; exact ⟨hu (w r) (fun i=>(hh i).1),ht (w r) (fun i=>(hh i).1)⟩
    let S : Calendar17 R Z s D x i:= ⟨m,Y,hm,hY,w,j,H',q,v,by convert hq using 1;norm_num,hv.mono (by norm_num),by
         filter_upwards [hs] with r hr; filter_upwards [hr] with p hh
         obtain ⟨⟨y,hy,_⟩,z,hz,_⟩:= hh; exact ⟨y,z,hy,hz⟩⟩
    exact ⟨⟨S,X,hX,hs⟩⟩
variable (U:Rift R Z s D x i)
-- real coupled projected trace horizon. Choose any pole. SAME capture outputs.
omit fx h W Z
set_option maxHeartbeats 600000 in
lemma inkPunch {j:ℕ×ℕ} {b: K→«Cover»} {n k l:ℕ}{z:R.family.label 0}{r:ℝ}(P:punchDebt R L w q b r j n k z)(hl:n ≤ l)(hk:l ≤ k) : ‖stamp17 R L w b r j l (hk.trans P.feeds) - send0 R.family z‖ ≤ q r / 2 / (Bid.gainChart R.family.path k l):=by
    obtain ⟨X,hX⟩:= P.prime; obtain ⟨⟨e,hx,hE,hU⟩,hw,hP⟩:=hX l hl hk
    change stamp17 R L w b r j l (hk.trans P.feeds) - send0 R.family z=(X l).x 0 at hP; rw [hP]
    apply le_trans _ hU; have hv:= rem_nonneg hE; refine le_trans ?_ (le_add_of_nonneg_left hv); exact Finset.single_le_sum (fun i _=> norm_nonneg ((X l).x i)) (Finset.mem_univ _)
-- price reached along all radii supported for given Stand sparse. Can only shrink ae horizon afterwards.
structure Sparkfare (U:Rift R Z s D x i) (e:ℝ) where
   l : ℝ→ℕ
   field : Height R.family.S home OPE.run l 1
   meets : ∀ᶠ r in home, U.X r ≤ l r ∧ l r < U.plan.m r ∧ ∀ᶠ t in L.lens, U.plan.q r / 2 / (Bid.gainChart R.family.path (U.plan.m r) (l r)) ≤ role R.family r * ledgerCoupling L r t ^ e
include fx Z
lemma glowPunch (e:ℝ): Nonempty (Sparkfare R Z x i U e):=by
    have hR : RateIs home OPE.run V 0:= ((goingWheel R Z fx).mesh.div (show RateIs home OPE.run id (-1) from loglife (r:=id) (show home ≤ home from le_rfl))).swap (by ring)
    obtain ⟨y,hy,hV⟩:= pole R.family U.plan.nearby.spine ((U.plan.plume.div (RateIs.const (c:=2) ageLarge (by positivity))).swap (by ring)) ((hR.mul (Z.coarse_g.rpow e)).swap (by ring)); refine ⟨⟨y,hy,?_⟩⟩
    filter_upwards [U.pace.earlier (by norm_num) ageLarge hy,hV] with r hr he
    exact ⟨hr.le,he.1, ((Z.fuse_at r).mono_left L.certified|>.rpow_const (.inl (Z.positive r).ne')|>.const_mul (role R.family r)).eventually (le_mem_nhds he.2)⟩
-- *still open.* Cross ask, along paid ancestor same height-as-r. no shortcuts.
omit fx
section
variable (e:ℝ)(M:Sparkfare R Z x i U e)
structure Prism {A':Ports R.family}(b:Beam R A' p):Prop where
    lands : 2 < e
    blend : ∃ (a:ℝ)(k:ℕ),0≤a∧∀ᶠ r in interval D s,∀ᶠ j in L.lens,∀ ht:M.l r ≤ j.1,
       ‖stamp17 R L U.plan.wage (nextRail C x 0 i r) r j (M.l r) ht-stamp17 R L U.plan.wage (baseRail C x r) r j (M.l r) ht-(vice (L:=L) R b i r (bee C x 0 i r) j-vice (L:=L) R b i r (ay C x r) j)‖ ≤ role C r*(a*ledgerCoupling L r j ^e*Z.Λ r^k)
lemma refracts {A':Ports R.family}(b:Beam R A' p) (hP:Prism R Z x i p U e M b) : Coupon R Z x i p U.plan b:=by
    have hl : T ≤ home:= (homes D).comp s.cofinal
    obtain ⟨a',k,he,hV⟩:=hP.blend
    constructor; refine ⟨a'+2,e,k,by positivity,hP.lands,?_⟩
    filter_upwards [hV,U.measure,M.meets.filter_mono hl,positiveLength.filter_mono hl] with r hr hU ht hv
    filter_upwards [hr,hU,ht.2.2,((Z.fuse_at r).mono_left L.certified).eventually (le_mem_nhds (Z.positive r))] with p hP hm hr hx
    obtain ⟨⟨y,hy,hC⟩,z,hz,hC'⟩:= hm; let j:=M.l r; have hJ:j ≤ p.1:= ht.2.1.le.trans hC.feeds
    refine ⟨y,z,hy,hz,?_⟩; let Z₀:=stamp17 R L U.plan.wage (baseRail C x r) r p j hJ; let Z₁:=stamp17 R L U.plan.wage (nextRail C x 0 i r) r p j hJ; let Y₀:=send0 C y; let Y₁:=send0 C z; let b':=vice (L:=L) R b i r (bee C x 0 i r) p-vice (L:=L) R b i r (ay C x r) p
    change ‖Y₁-Y₀-b'‖ ≤ _;rw [show Y₁-Y₀-b'= (Z₁-Z₀-b')+((Z₀-Y₀)-(Z₁-Y₁)) from by ring]; have ht' : U.plan.q r /2 / _ ≤ role C r*(ledgerCoupling L r p ^e*Z.Λ r^k):= hr.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hx _) (one_le_pow₀ (Z.above r))) (div_pos (R.family.S.a_pos _) hv|>.le))
    exact (norm_add_le ..).trans ((add_le_add (hP hJ) ((norm_sub_le ..).trans (add_le_add ((inkPunch R _ _ hC ht.1 ht.2.1.le).trans ht') ((inkPunch R _ _ hC' ht.1 ht.2.1.le).trans ht')))).trans_eq (by ring))
end
end YM.RG17
