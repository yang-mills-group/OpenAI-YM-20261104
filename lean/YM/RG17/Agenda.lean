import YM.RG17.Fair
/-!
# Agenda

 Primary payoff -> continuum Beam. Need actual M from **within**
 PaidAt proof comparing forecasts; existence of such M already (but
 not of alignment with independent expansion). This does not
 change Ports or the anomaly signal needed. Exact cal norm & Mesh/horizon
 matching. Compiling fallout theorem.
-/
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
-- volume price before regulator limit
abbrev duty (L:Layout F)(m Y:ℝ→ℕ) (w:podium R) (q v:ℝ→ℝ)(b: K → «Cover») (z:R.family.label 0)(r:ℝ)(i:ℕ×ℕ):=
       let u(j):=atRef L 4 r i (w r j);
       CollectionR R (fun _:Fin 2=>4) 0 r i.1 i.2 (wrap (R.family.side (wheel R.family r) i.2) ∘ b) u (q r) (v r) (Y r) (m r) z
include W
lemma readoutEarns (r:ℝ)(b: K → «Cover»)(z:R.family.label 0)(j:ℕ×ℕ) (hj: Q r ≤ j.1)(ht:R.family.ref 0 ≤ j.1)(h:duty R L m Y w q v b z r j) : ‖chem (L:=L) R w r b j - (keyMass R.family j.1 j.2 :ℂ)*send0 R.family z‖ ≤ keyMass R.family j.1 j.2 * v r:=by
    let N:= j.1; let P:=j.2; let F':=Config G (R.family.side N P)
    let V':= rake R b r j; let Q':= keyMass C N P
    let E:= shutter R L A r N P (w r); let g (U:F'):= ∏ i:K,R.family.seen (E i) (V' i) U; let α:= R.family.beta N P; let y:=send0 C z
    have hh : R.family.O N P z (0:Site _)= (fun _=> y):=by
       obtain ⟨c,hc⟩:= RG12.unit_spans W.simpleGate C 0 (R.family.ref 0) (by decide) z
       change z=c • R.family.refUnit 0 at hc; unfold y; rw [hc,map_smul,(R.family.linearO N P 0 (0:Site _)|>.map_smul c _ : R.family.O N P (c • R.family.refUnit 0) (0:Site _) = _),R.family.constant R.makes 0 ht (p:=P), show send0 C (R.family.refUnit 0)=(1:ℂ) from ?_]; rfl -- `y`
       simp only [Family.refUnit,Source.unitVec,pow_zero, one_smul]; rfl
    let φ:=fun u=> g u-R.family.O N P z 0 u
    have hb:(∫ U,φ U∂law G (R.family.side N P) α)=R.family.numeric N P E V'-y:=by
       unfold φ; rw [hh,integral_sub ((show Continuous g from continuous_finsetProd _ (fun i _=> R.family.continuousO ..)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)) (integrable_const _),integral_const]; simp; rfl
    let B':=Cells.center R.family.S P h.load.live 0
    have he:‖moment α φ‖ ≤ v r:=by
       have hx':= h.load; change OPE.Cards.PaidAt R.family.S N P _ α (v r) φ at hx'
       apply le_trans (b:=B'.rootTest α φ) _ hx'.mark
       simpa [Fin.prod_univ_succ] using! B'.planted (seamless R.makes N P) (fun _ : Fin 1 => 0) (fun i j _=>Subsingleton.elim _ _) (fun _ => φ) (fun _ => hx'.ticket)
    have hu:chem (L:=L) R w r b j=(Q':ℂ)*R.family.numeric N P E V':= fullDimes R.makes E V' hj
    rw [hu]; change ‖(Q':ℂ)*_-(Q':ℂ)*_‖ ≤ Q' * v r; rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ Q' from (partition_pos _).le)]
    exact mul_le_mul_of_nonneg_left (by rw [← (hb : moment α φ=_)]; exact he) ((partition_pos _).le)
-- domain hypothesis; m,Y and rates purchased already. need same output in target. Any pair okay.
structure Calendar17 (Z:Ledger L)(s:Extraction.Sequence)(D:Lenses.Mantle F B)(x:Points 2)(i:Axis) where
    m : ℝ→ℕ
    Y : ℝ→ℕ
    nearby : Lookup R m
    half : Height R.family.S home OPE.run Y (1/2)
    wage : podium R
    wageLevel : ℕ
    wagePrice : ∀ᶠ r in interval D s, ∀ j:Fin 2,Paid (d:=fun _=>4) L r (wage r) j ≤ H (Q r)^wageLevel ∧ master L 4 r (wage r j)=portal L r (blue R.family i j)
    q : ℝ→ℝ
    v : ℝ→ℝ
    plume : RateIs home OPE.run q 0
    going : RateLE home OPE.run v (-(1/32))
    tickets : ∀ᶠ r in interval D s,∀ᶠ t in L.lens,∃ y z:R.family.label 0,duty R L m Y wage q v (baseRail R.family x r) y r t ∧ duty R L m Y wage q v (nextRail R.family x 0 i r) z r t
variable (h:Stands L D s)
include h Z W fx
lemma appointments (hp:x∈generic 2): Nonempty (Calendar17 R Z s D x i):=by
    obtain ⟨m,hm⟩:= leasable R Z fx; obtain ⟨Y,hY⟩:= found ageLarge (R.family.path.levels.fits.mesh) (by norm_num : (0:ℝ) ≤ 1/2)
    obtain ⟨j,w,H'⟩:= grantedWays R Z fx (fun _=>4) (blue R.family i) W h
    obtain ⟨q,v,hq,hv,hV⟩:=assures R Z fx W (0:Fin 2) (fun _=>4) j 0 Y m h hm hY; have hl:T ≤ home:= (homes D).comp s.cofinal
    refine ⟨⟨m,Y,hm,hY,w,j,H',q,v,by convert hq using 1;norm_num,hv.mono (by norm_num),?_⟩⟩
    filter_upwards [H',hV x (baseRail R.family x) hp ((reachesBase Z fx x).mono_left hl),hV x (nextRail R.family x 0 i) hp ((reachesNext Z fx x 0 i).mono_left hl)] with r hh hu ht
    filter_upwards [hu,ht] with p hu ht
    obtain ⟨y,hy⟩:=hu (w r) (fun i=>(hh i).1); obtain ⟨z,hz⟩:=ht (w r) (fun i=>(hh i).1); exact ⟨y,z,hy,hz⟩
variable (U:Calendar17 R Z s D x i)(e:ℝ)
omit W h
include U fx
private lemma warrants : ∀ᶠ r in home,∀ᶠ t in L.lens, U.v r ≤ (V r)*ledgerCoupling L r t^e:=by
    have hR : RateIs home OPE.run V 0:= ((goingWheel R Z fx).mesh.div (show RateIs home OPE.run id (-1) from loglife (r:=id) (show home ≤ home from le_rfl))).swap (by ring)
    have hx:= U.going
    filter_upwards [(hR.mul (Z.coarse_g.rpow e)).overtakes hx ageLarge (by simp),positiveLength] with r hr ht
    exact (((Z.fuse_at r).mono_left L.certified|>.rpow_const (.inl (Z.positive r).ne')|>.const_mul (V r)).eventually (le_mem_nhds hr))
structure Coupon {A':Ports R.family}(C':Calendar17 R Z s D x i)(b:Beam R A' p):Prop where
    buys : ∃ (a e:ℝ)(k:ℕ),0≤a∧2<e∧∀ᶠ r in interval D s,∀ᶠ t in L.lens,∃ y z:R.family.label 0,duty R L C'.m C'.Y C'.wage C'.q C'.v (baseRail R.family x r) y r t ∧ duty R L C'.m C'.Y C'.wage C'.q C'.v (nextRail R.family x 0 i r) z r t ∧
        ‖send0 R.family z-send0 R.family y - (vice (L:=L) R b i r (bee R.family x 0 i r) t-vice (L:=L) R b i r (ay R.family x r) t)‖≤ role R.family r*(a*ledgerCoupling L r t ^e* Z.Λ r^k)
include U W
lemma budgets {A':Ports R.family}(b:Beam R A' p) (hB:Coupon R Z x i p U b) : Emission (B:=D) R Z s b x i:=by
    have hl:T ≤ home:= (homes D).comp s.cofinal
    obtain ⟨a',e,k,he,hk,hV⟩:= hB.buys
    constructor; refine ⟨U.wage,U.wageLevel,2+a',e,k,by positivity,hk,U.wagePrice,?_⟩
    filter_upwards [hV, (warrants R Z fx x i U e).filter_mono hl,positiveLength.filter_mono hl] with r hr hU hT -- e args
    filter_upwards [hr,hU,(large_mesh f (Q r)).filter_mono L.certified,(large_mesh f (R.family.ref 0)).filter_mono L.certified, ((Z.fuse_at r).mono_left L.certified).eventually (le_mem_nhds (Z.positive r))] with t hi ht hn hq hx m
    obtain ⟨y,z,hy,hz,hY⟩:= hi
    let X₀:=chem (L:=L) R U.wage r (baseRail C x r) t; let X₁:=chem (L:=L) R U.wage r (nextRail C x 0 i r) t; let Y₀:=send0 C y; let Y₁:= send0 C z; let c:ℂ:=(m:ℂ); let P:= vice (L:=L) R b i r (bee C x 0 i r) t-vice (L:=L) R b i r (ay C x r) t
    change ‖X₁-X₀-c*P‖ ≤ _
    rw [show X₁-X₀-c*P=(X₁-c*Y₁)-(X₀-c*Y₀)+ c*((Y₁-Y₀)-P) from by ring]
    have hm: 0 ≤ m:= (partition_pos _).le
    have he' : ‖c*((Y₁-Y₀)-P)‖ ≤ m*(role C r*(a'*ledgerCoupling L r t ^e*Z.Λ r^k)):=by rw [norm_mul,show ‖c‖=m from Complex.norm_real _ |>.trans (Real.norm_of_nonneg hm)]; exact mul_le_mul_of_nonneg_left hY hm
    apply (norm_add_le ..).trans
    refine (add_le_add ((norm_sub_le ..).trans (add_le_add (readoutEarns R (L:=L) W _ _ _ _ _ r _ z t hn hq hz) (readoutEarns R (L:=L) W _ _ _ _ _ r _ y t hn hq hy))) he').trans ?_
    have ht : U.v r ≤ role C r*(ledgerCoupling L r t ^e*Z.Λ r^k):= ht.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (Real.rpow_nonneg hx _) (one_le_pow₀ (Z.above r))) (div_pos (R.family.S.a_pos _) hT|>.le)); refine (add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left ht hm) (mul_le_mul_of_nonneg_left ht hm)) _).trans_eq ?_; ring
omit U
include h
lemma foretold {A':Ports R.family}(b:Beam R A' p) (he:x∈generic 2)(hz:bright R.family x≠0)(hp:2 ≤ p)(hY:∀ i,∃ U:Calendar17 R Z s D x i, Coupon R Z x i p U b)(hf:Tendsto (fun r=> drum R.family x (aurora R Z b) r/(Z.g r:ℂ)^2) (interval D s) (𝓝 ((anomalyCoefficient G/2) • bright R.family x))) : SampleLog F T (theoryDensity G) ∧ 0<theoryDensity G ∧ ∀ (m:ℕ)(U:F.action.operators.H →ₗᵢ[ℂ] Shell.Sum m),¬ Shell.Comparison F (meanExact F) U:=
  circles R W Z h fx b hp he hz (fun i=>budgets R Z fx W x i p (hY i).choose b (hY i).choose_spec) hf
end YM.RG17
