import YM.WilsonCoeffUV.Emit.PhysicalClock
import YM.WilsonCoeffUV.Stable.Analytic.Supply
import YM.WilsonCoeffUV.Root.UV.HorizonD
/-! # Exact formal prescription for primary packet: compact K-component interface

Spout is literal (coupling reclosure ****after**** Wick), relative contacts within centered cube of
current mesh. Summing preimages before extracting projection; keeps y labels. No truncation losses
in the linear identities. One mark here. Also respects gauge changes and joint signed readings on
finite tori under the hypotheses in Root/Step/Pivot. This file collects the equations in root-alphabet frame conventions;
later R users should NOT use this as a density term in actual T^-1 until after real comparison.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{h D k h' i j m b N e:ℕ}{F:Frame G h}{T:SectionData F}{p:h<D} {H:Hol G}{s A C t:ℝ}

lemma rootArgument (V : Volume D)(U: Type)(P:Pal (Vote D) U)(x:Cost):
    jot V (Blue.mix x P)=Blue.mix x (jot V P):=by ext i r q; rw [jot_here]; simp_rw [Blue.mix,Finset.sum_apply,Pi.smul_apply,_root_.sum_apply,_root_.smul_apply, jot_here]
-- product tests Xi separately in current smooth-only root. engineering explicit.
lemma sampledRoot (G:Gauge)(P:Patch)(w:Site P.L)(n:Side)(Z:Vell G n D) (X:Scroll D)(p): jot (page D X) (gatherT P w p Z)= fun i r=> revolve p (jot (page D (growWord P w D X)) Z i r) :=by
    funext i r y; rw [←observed]; rfl

-- one-unit compensated formula relative to true stamp; density total excludes
-- exponential flat free-g ratio (cancels identically before extracting).
lemma contractMark (P:Patch)(K:KernelChoices)(H:FaceRow)(Q:(n:Side)→ Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)(Ñ:ChartRatio G)(n:Side)(k h:ℕ)(Z:Vell G (n*P.L) D)(A:PChart G (n*P.L))(u:shellK k Z)(p:P.Branches K G)(g:LocalRatio Ñ)(v:shellK 2 A)(q:∀ i,Pure (A i))(r:∀ i,Pure (Z i))(hp:(H.acts (n*P.L)).transpose=H.acts (n*P.L))(X:Scroll D) (x:Cost):
    let b:=page D X; let Y:= stepAt P K n; let F:=xree P K n
    let W:=inside Y F H (Q n) Ñ A
    IsUnit W ∧
    let V:= gradeH P h k • Blue.mix x (collarT P K Ñ H Q k D A Z); let t:= (P.L.val:ℝ)^h/(P.L.val:ℝ)^4
    redo (U:=Woods G n) x W*flash (jot b V)=
     redo x (t • ∑ w:Site P.L,insideMark Y F H (Q n) Ñ A (jot b (gatherT P w (wrap (n*P.L) (lift w)) Z))):=by
    intro b Y F W
    refine ⟨?_,?_⟩; · apply PowerSeries.isUnit_iff_constantCoeff.mpr; rw [show constantCoeff W=1 from inside_mass Y F H (Q n) g]; simp
    intro V t; let T:= collarT P K Ñ H Q k D A Z; let z (w:Site P.L):= bellOne P K Ñ H Q k D (n:=n) w A Z
    have hr w: shellK k (z w):= pin_swell P K Ñ H Q k k g w A Z v u
    have hT:shellK k T:= pin_test P K Ñ H Q k k g A Z v u
    unfold V; rw [map_smul, flash_mu _ (jot_length _ (mix_length hT)),rootArgument,←redo_stern _ (jot_length _ hT),←redo_μ x (gradeH P h k),←map_mul]
    apply congr_arg; change W * (gradeH P h k • flash (jot b (tiara P k • ∑ w:Site P.L,z w)))=_
    rw [map_smul,map_sum, flash_mu _ (shelf (fun i _=>jot_length _ (hr i))), smul_smul, gradeBB, mul_smul_comm, flash_term _ (fun i _=>jot_length _ (hr i)), Finset.mul_sum]; refine congr_arg (fun p=>t • p) ?_; refine Finset.sum_congr rfl (fun i _=>?_)
    let R:=gatherT P i (wrap (n*P.L) (lift i)) Z
    let S:=jot b R; have hm: jot b (z i)= reed Y F H (Q n) Ñ A k S:= reed_maps Y F H (Q n) k (((ContinuousLinearMap.apply ℝ ℝ) b).toLinearMap); rw [hm]
    exact (inside_reed Y F H _ k v g (jot_length _ (gather_mark P Z i _ u)) p hp q (fun _=>jot_code b (W:=R) (gather_pure P Z i _ (r _)))).symm

-- wrapper for EXACT at actual stamps (notation unspecified calendar). Every permitted torus.
theorem evaluatedPrimary (A:Levels G)(Ñ:ChartRatio G)(g:G.Simple)(H:LocalRatio Ñ)(hm:m<N)(F:TowerS G D)(h k:ℕ)(hF:On k F) (n:Side)(X: Scroll D):
    let P:= ll A m; let K:=A.clock.kernel; let W:= stepAt P K n; let T:=xree P K n
    let R:=freeForms A N (m+1); let Q:= roam A N m n
    let u:= ratioHigh A Ñ N m; let Z:= (story A Ñ N (m+1)).1 (n*P.L)
    let C:=inside W T R Q Ñ Z; let i:=page D X; IsUnit C ∧ constantCoeff u=1 ∧
    redo (U:=Woods G n) u C * flash (jot i ((Spout A Ñ N m h k F).1 n)) =
        redo u (((P.L.val:ℝ)^h/(P.L.val:ℝ)^4) • ∑ w:Site P.L,insideMark W T R Q Ñ Z (jot i (gatherT P w (wrap (n*P.L) (lift w)) (F.1 (n*P.L))))) :=by
   intro P K W T R Q u Z C i; let q:=(old A Ñ g H N (m+1) hm).basis (n*P.L)
   obtain ⟨h,v⟩:=contractMark P K R (roam A N m) Ñ n k h (F.1 (n*P.L)) Z (hF.launch _) (A.blocks m 0).branches H q.lamp q.shape (hF.evenS _) (age_sym A ..) X u
   exact ⟨h, back_cc (angle_tilt g H hm),v⟩

abbrev starting (T:SectionData F)(p:h<D):Island F D:= (fun n i=>herald T p i n, anthem T p)
abbrev bare (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(N m:ℕ):= walkY A Ñ N m (N-m) (starting T p)
lemma birthFormula (T:SectionData F)(p:h<D)(t:T.Sound H)(b:Bid.pop T)(n:Side)(x:Scroll D)(j: Alma F): let K:=knurl (notar F j); let X n j:=(starting T p).1 n j; PowerSeries.X^valence F j * flash (jot (page D x) (X n j))= crease x K 0 • jet (fun Y:Lawn (Woods G n)=> (T.places (Pi.single (sheet F j) 1) 0 (mantle Y)).re):=by
    intro K X; exact herald_lit T p j n (page D x) b H t
variable {E W X:Credit}
/-- From calibration computed at a genuine position, with the prescribed transport. Does not mean actual nonperturbative maps at this root. -/
theorem matrices_from_actual_root (L:Theatre H T p e E W)(p0:L.V.anchor ≤ m)(w:m≤b)(u:b≤N):
    let A:= L.V.draws; let Ñ:=L.V.paid; let B i:= prismata F (bare A Ñ T p N i).2
    let C:=CurNames A Ñ T p N m (b-m) false
    IsUnit (B m).det ∧ IsUnit (B b).det ∧ C=B m*(Chars F (relativeF A Ñ N m (b-m)) (B b))⁻¹ ∧ Peaks A Ñ T p N m= imprint (bare A Ñ T p N m) (B m)⁻¹ :=by
    intro A Ñ B C
    have he j (h0:j≤N)(v:L.V.anchor≤ j):B j=CurNames A Ñ T p N j (N-j) false ∧ bare A Ñ T p N j= imprint (Peaks A Ñ T p N j) (B j)∧ IsUnit (B j).det:=by
       have hg:j+(N-j)=N:= Nat.add_sub_of_le h0
       have ht := cornea L v (show j+(N-j)≤ N from hg.le)
       have hx:=compatibleN L v (show j+(N-j)≤ N from hg.le); have hy:=ebbing L v (show j+(N-j)≤ N from hg.le) false; unfold Theatre.lore at ht hx; rw [hg,Peak_initial] at hx ht; refine ⟨ht, hx.trans (by rw [show B j=_ from ht]),?_⟩; rw [show B j=_ from ht]; exact hy.1
    obtain ⟨ℓ,hx,s⟩:= he m (w.trans u) p0; obtain ⟨_,hv,g⟩:=he b u (p0.trans w)
    let R:= Chars F (relativeF A Ñ N m (b-m)); let Y:=L.lore N m
    have ht: bare A Ñ T p N m=walkY A Ñ N m (b-m) (bare A Ñ T p N b) := by
       -- decomposition, via walkY recursion
       clear ℓ hx s hv g he
       induction w using Nat.decreasingInduction with
       | self=> rw [Nat.sub_self]; rfl
       | of_succ m h ih=>
            have h₁:N-m=N-(m+1)+1:=by omega
            have h₂:b-m=b-(m+1)+1:=by omega
            rw [bare,h₁,walkY,h₂,walkY]; exact congr_arg (Cosmos.descend _ _ _ m) (ih (by omega))
    have hz:= prang L p0 (show m+(b-m)≤ N by omega) (B b); rw [Nat.add_sub_of_le w] at hz; rw [hv,hz] at ht
    let U:=R (B b)
    have hm:= (production L (w.trans u) p0).1; have hQ:B m=C*U:=by
        change prismata _ _=_; rw [ht]; dsimp only [imprint]; change prismata F (impose Y.2 _) = _; rw [prismata_bind F _ (fun i=>solo_stretch (hm.scan.solo i)), hm.era, _root_.one_mul]
    have hS:IsUnit U.det:= isUnit_of_mul_isUnit_right ((Matrix.det_mul C U) ▸ (hQ ▸ s) : IsUnit (C.det*U.det))
    refine ⟨s,g,?_,?_⟩
    · rw [hQ,Matrix.mul_assoc,show R (B b)=U from rfl,Matrix.mul_nonsing_inv _ hS,Matrix.mul_one]
    rw [hx,imitive,Matrix.mul_nonsing_inv _ s,completeF]
end YM.WilsonCoeffUV.RootLaw
