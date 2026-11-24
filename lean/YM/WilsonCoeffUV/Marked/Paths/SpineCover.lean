import YM.WilsonCoeffUV.Marked.Paths.Meteor
/-!
# Spine theorem at a particular origin. No lost valence. Uses ROOTED wind.
Deduction for Auth via float period certificates all powers.
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Work.F03
variable {G:Gauge}{n:Side}{k h r t i j e:ℕ}{s A B:ℝ}
variable {V W I α β:Type}[NormedAddCommGroup V][NormedSpace ℝ V]

-- vertical CPT. Mural via pulse. Later limiting only arcs (Era cert beyond all). need invariant on germs too.
lemma pagoda {P:Era G V} (p:Auth h P)(i:ℕ): pillar P.2 i:=by
    intro b x; let A:= ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal i, (wickLamp b 0 (x,v) j z.1 (P.2 z.2) + wickLamp 0 b (x-step v,v) j z.1 (P.2 z.2))
    funext j y; apply probe; intro L; simp only [Pi.zero_apply,map_zero]; let Q:=tuftV L P; let R j:=cloaks L.toLinearMap (P.2 j)
    change cloaks L.toLinearMap A j y=_
    have hx : cloaks L.toLinearMap A=0:=by unfold A; simp_rw [map_sum,map_add,wick_maps]; exact Auth.roots (p.tuft L) b x i
    rw [hx]; rfl
lemma pigment {P:Era G V} (p:Auth h P)(i r) : mural (P.2 i r):= by
    intro f v x; apply probe; intro L
    let Q:=tuftV L P; have he:=p.tuft L
    let D (w:Fin r→G.ColorIndex):=fun j=>stone (v j) (w j); let b (u:Fin r→G.ColorIndex):=∏ i,gammaC f (u i) (x i)
    have hx n : Q.1 n i r (slideC n (D x))=∑ u:Fin r→G.ColorIndex,b u • Q.1 n i r (slideC n (D u)):= shot_card (Q.1 n) (he.safe n) (he.span n) (he.pale n) f _ _ (fun i=>(wrap n ((v i).1), (v i).2)) x
    have hv u:Tendsto (fun n=> Q.1 n i r (slideC n (D u))) atTop (𝓝 (Q.2 i r (D u))):=(he.wing i r).point _
    simp_rw [map_sum,map_smul]; exact tendsto_nhds_unique (hv x) ((tendsto_finsetSum _ (fun i _=> (hv i).const_smul (b i))).congr fun n=> (hx n).symm)
lemma shadest (T:Ten V (YForest G) r)(h:mural T)(x:RadP G r): shadeStar (meteor T x):=by
    obtain ⟨x,p⟩:=x; let b:= (∏ j,glisten (p j)); intro L u X; let P:=dip (meteor T ⟨x,p⟩) L
    let Q:= P.coeff
    have hx i: Q i=b* L (T (terrace G r (x,i))):= by change L (b • _) = _; rw [map_smul]; rfl
    have hp i: Q i=∑ j,(∏ k,gammaC u (j k) (i k)) • Q j:=by
       rw [hx]; simp_rw [hx]; unfold terrace; simp only [Equiv.coe_fn_mk]; rw [h u x i]; simp_rw [map_sum,map_smul,Finset.mul_sum,smul_eq_mul]; apply Finset.sum_congr rfl; intro j _; ring
    have hh j i: G.adjoint u (X j) i=∑ a,gammaC u i a*X j a:= (show _= (gammaC u *ᵥ ((coatC G).symm (X j))) i by rw [gammaC, LinearMap.toMatrix'_mulVec]; rfl)
    change ∑ i,Q i * ∏ j,G.adjoint u (X j) (i j)=∑ i,Q i *∏ j, X j (i j)
    conv_rhs=> arg 2; intro i; arg 1; rw [hp i]
    simp_rw [hh, Fintype.prod_sum,Finset.mul_sum,Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; simp only [Finset.prod_mul_distrib,smul_eq_mul]; ring
lemma wind_p {P: Era G V}(p:Auth h P)(u:∀ i<e,P.2 i=0): ∀ j (v:r=j+1) x k,windsL (r:=j) x k (v ▸ P.2 e r)=0 := by rintro j rfl; exact sky_split (fun v x i=> pagoda p i v x) p.coverP e j (fun i hi r _=> by rw [u i hi]; rfl)
section
-- colour fold before address. unique
lemma caustic_abs (X:Atom G r)(p:Site n)(A:Link G n) : caustic (rye (meter X p) r) (fun _=>A)= X.poly (fun i=>faceCurl (slotFace (X.leg i) p) (arm G n 1 A)):=by
    let T:= meter X p; have hp:= rayon T r A; rw [jet_apply] at hp
    have he: caustic (rye T r) (fun _=>A)=MvPolynomial.eval A (paint r (rye T r)):=by rw [paint,toll]; unfold caustic; exact Finset.sum_congr rfl fun i _=> mul_comm ..
    rw [he,hp]; change Tensor.diagonal (Tensor.coeff (meter X p) r 0) A=_
    rw [meter_lift,Tensor.symmetrize_diagonal]; exact ink_note ..
lemma noteP (C:Comet G V r)(n:Side)(L:V→L[ℝ]ℝ)(v:Link G n): L (caustic (sapR C n r) (fun _=>v))= (dip C L).poly (fun i=> faceCurl (slotFace (C.sl i) 0) (arm G n 1 v)):=by
    unfold caustic; simp_rw [map_sum,map_smul,sap_view]; exact caustic_abs ..
lemma kilt (T:Ten V (YForest G) r)(v:Link G n)(x:Panel r) : ∑ a:Stationary.Ink G r, pressOn T (fun _=>allS v) (terrace G r (x,a)) = ∑ p:RouteP G x, caustic (sapR (meteor T ⟨x,p⟩) n r) (fun _=>v) :=by
    apply probe; intro L; simp_rw [map_sum, pressOn, map_smul, noteP, Atom.poly]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; let f:= fun j=> stone (x j) (i j); let Q j (v:wordBand G (x j)):= bladeP v; let Z:= T f
    change (∏ j,allS v (stone (x j) (i j))) • L Z = ∑ p:RouteP G x,_
    simp_rw [balanced]; rw [Fintype.prod_sum,Finset.sum_smul]; apply Finset.sum_congr rfl; intro j _; rw [Finset.prod_mul_distrib]; change (_ * _) • L Z = L ((∏ k,glisten (j k)) • Z)*_; rw [map_smul]; change _*L Z=( (∏ k,glisten (j k))*L Z) * ∏ b, (faceCurl (slotFace (bladeP (j b)) _) _ : G.Color) (i b); ring
lemma coe_opt (P Q:Ten V (Woods G n) k)(p:Smooth P)(q:Smooth Q)(h:∀ A:Link G n,caustic P (fun _=>A)=caustic Q (fun _=>A)): P=Q:=by
    funext x; apply probe; intro L
    have ht T : ∀ a:Link G n,MvPolynomial.eval a (paint k (L ∘ T))= L (caustic T (fun _=>a)):=by intro a; rw [paint,toll,caustic,map_sum]; simp_rw [map_smul]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
    apply congr_fun (unique_kernel (P:=L ∘ P) (Q:=L ∘ Q) (fun i x=>congr_arg L (p i x)) (fun i x=> congr_arg L (q i x)) (MvPolynomial.funext fun A=> by rw [ht,ht,h])) x
end
variable [CompleteSpace V]
lemma beginsA (X: I→Comet G V k)(p:SumBudget (fun i=>integerP (X i) s) A)(h:0<s)(e:ℕ)(n:Side)(v:Link G n): HasSum (fun i=> caustic (sapR (X i) n k) (fun _=>v)) (caustic ((bolus X e).1 n e k) (fun _=>v)):=by
    unfold caustic; have hx x i: (volumeR (X x) e).1 n e k i=sapR (X x) n k i:=by change moved _ _ _ _ _ _= _; rw [moved,if_pos le_rfl,Nat.sub_self,add_zero,shine_lit]
    apply hasSum_sum; intro x _; apply HasSum.const_smul _ _; simp_rw [← hx]; exact elevated h p e n e k x
lemma flow_meter (T:Ten V (YForest G) k)(p:Twig 0 s A T)(h:0<s)(r:Smooth T)(q:mural T)(u:∀ j (v:k=j+1),∀ x c,windsL (r:=j) x c (v ▸ T)=0)(e:ℕ) (n:Side): (bolus (meteor T) e).1 n e k=plume T n:=by
   let X:= meteor T
   have hp := floatPrice p h
   have hs:= mist h k
   have hx : Auth k (bolus X e):= Mer.Rolls.stars hs hp (Nat.le_add_right _ _) (shadest T q)
   apply coe_opt _ _ (hx.pale n e k) (rounding n T r); intro a; let L:= terrace G k
   have ht:= beginsA X hp hs e n a; rw [← ht.tsum_eq]; rw [chordal T p h,show (fun _ :Fin k=>a∘ foldUnder n)=(fun _=> insideP a) from rfl, ←tonicP T (fun _=>a) p h r u]
   let U:=pressOn T (fun _=>allS a); let S:= U ∘ L; let Y b:=caustic (sapR (X b) n k) (fun _=>a)
   have hh : Summable S:= L.summable_iff.mpr ((pluck_profit p h (fun _=> wagesAll a)).of_norm: Summable U)
   rw [pluck,ht.summable.tsum_sigma,← L.tsum_eq]; change _= tsum S; rw [hh.tsum_prod]; exact tsum_congr fun b=>by change (∑' j,Y ⟨b,j⟩)=_; rw [tsum_fintype,tsum_fintype]; exact Eq.symm (kilt T a b)
lemma flowing (T:Ten V (YForest G) k)(p:Twig 0 s A T)(h:0<s)(r:Smooth T)(q:mural T)(u:∀ j (v:k=j+1),∀ x c,windsL (r:=j) x c (v ▸ T)=0)(e:ℕ): (bolus (meteor T) e).2 e k=T:=by
    let Q:= bolus (meteor T) e; have hp:= floatPrice p h; have he:= (Mer.Rolls.stars (mist h k) hp (Nat.le_add_right k e) (shadest T q)).wing e k
    exact (he.congr (Eventually.of_forall fun n=> flow_meter T p h r q u e n)).exten (caisson p h)
lemma enclave {P:Era G V}(p:Auth k P)(u:∀ i<e,P.2 i=0)(j:ℕ)(hx:Cork Bank.terrain 0 s A (P.2 e j))(hp:0<s) : (bolus (meteor (P.2 e j)) e).2 e j=P.2 e j:= flowing _ hx hp (p.coverP e j) (pigment p _ _) (wind_p p u) _
end YM.WilsonCoeffUV.Mer.Rolls
