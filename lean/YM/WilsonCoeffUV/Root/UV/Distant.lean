import YM.WilsonCoeffUV.Root.UV.InverseTransfer
/-!
# Applying price on tori hierarchy after replacing limiting data. Quick ratios and matrix operators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}
section
variable {P Q:ℕ→Cost}{W X: Cost}
-- polynomial ops in variables. dual follows by old inf
lemma ChartRise (h:∀ i≤e,Rising P W i)(p:∀ i≤e,Rising Q X i): Rising (fun i=> chartB (P i) (Q i)) (chartB W X) e:=by
    unfold Rising; simp_rw [chart_coeff]; refine tendsto_finsetSum _ ?_; intro j hj; have he:= Finset.mem_range.mp hj; exact Tendsto.mul (h j (by omega)) (Rising.pow (P:=Q) (i:=e-j) (fun i hi=>p i (by omega)) (j+1))
lemma reelRise (h:∀ i≤e,Rising P W i)(p:∀ i≤e,Rising Q X i): Rising (fun i=> Bank.reel (P i) (Q i)) (Bank.reel W X) e:=by unfold Rising; simp_rw [reelQuote]; refine tendsto_finsetSum _ ?_; intro j hj; have he:= Finset.mem_range.mp hj; exact Tendsto.mul (p j (by omega)) (Rising.pow (P:=P) (i:=e-j) (fun i hi=>h i (by omega)) j)
lemma invertedRise (h:∀ i≤e,Rising P W i)(p:∀ᶠ n in atTop,chartB (P n) (Q n)=1)(q:chartB W X=1)(hp:∀ᶠ n in atTop,constantCoeff (P n)=1)(hw:constantCoeff W=1): Rising Q X e:=by
    induction e using Nat.strong_induction_on with
    | h e ih=>
      let S:= (Finset.range (e+1)).erase 0
      have hh F G (h:constantCoeff F=1)(p:chartB F G=1): coeff e G=coeff e (1:Cost)-∑ j∈S,coeff j F * coeff (e-j) (G^(j+1)):= by rw [← p,inflow h, add_sub_cancel_right]
      have hg j (p:j∈ S):j≤e∧e-j<e:= by obtain ⟨x,t⟩:= Finset.mem_erase.mp p; have he:= Finset.mem_range.mp t; omega
      unfold Rising; rw [hh W X hw q]; refine (tendsto_const_nhds.sub (tendsto_finsetSum (f:=fun j i=>coeff j (P i)*coeff (e-j) ((Q i)^(j+1))) S (fun j w=>?_))).congr' ?_
      swap; · exact (hp.and p).mono (fun n h=> (hh _ _ h.1 h.2).symm)
      exact Tendsto.mul (h j (hg j w).1) (Rising.pow (P:=Q) (i:=e-j) (fun i hi=> ih i (by have hh: e-j<e:= (hg j w).2; omega) (fun q q'=> h q (q'.trans (hi.trans (Nat.sub_le ..))))) (j+1))
end
section
variable (A: Levels G)(Ñ:ChartRatio G)
def towards (m k:ℕ):Cost := palmB (fun i=> back (viridian A Ñ (m+i))) k
def reveries (m k:ℕ):Cost:= leeB (fun i=>pace (viridian A Ñ (m+i))) k
end
lemma destiny (R:Realm G e E)(h:R.anchor≤m)(v:i≤ e)(k): Rising (fun n=>relativeF R.draws R.paid n m k) (towards R.draws R.paid m k) i:=by
    induction k generalizing i with
    | zero=> exact tendsto_const_nhds
    | succ k ih=> simp_rw [relativeF,towards,palmB]; exact ChartRise (fun i u=> Rising.back (fun j hv=>evergreen R (show R.anchor≤ m+k from by omega) (hv.trans (u.trans v))) ((eventually_gt_atTop (m+k)).mono fun n hn=> angle_tilt R.hG R.green hn) (one_sun R (show R.anchor≤m+k from h.trans (Nat.le_add_right ..)))) (fun i h=> ih (h.trans v))
lemma serenity (R:Realm G e E)(h:R.anchor≤m)(k): chartB (towards R.draws R.paid m k) (reveries R.draws R.paid m k)=1 ∧ chartB (reveries R.draws R.paid m k) (towards R.draws R.paid m k)=1:= deckDual _ _ (fun i _=> chart_forward (one_sun R (show R.anchor≤m+i from by omega))) (fun i _=> chart_backward (one_sun R (show R.anchor≤m+i from by omega)))
lemma hence (R:Realm G e E)(h:R.anchor≤m)(v:i≤e)(k): Rising (fun n=>relativeC R.draws R.paid n m k) (reveries R.draws R.paid m k) i:= by
    exact invertedRise (fun i hi=>destiny R h (hi.trans v) k) ((eventually_ge_atTop (m+k)).mono (fun _ g=>(direction R.hG R.green g).1)) (serenity R h k).1 ((eventually_ge_atTop (m+k)).mono fun _ g=> angularF R.hG R.green g) (cc_palm (n':=k) (fun i _=> back_cc (one_sun R (show R.anchor≤m+i from by omega))))
def beckon (A:Levels G)(Ñ:ChartRatio G)(m k:ℕ)(b:Bool)(i:ℕ):= if b then reveries A Ñ (m+i) (k-i) else towards A Ñ m i
def arrowV (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(m k:ℕ)(b:Bool): Coil F:= steepen (fun i=> Chars F (beckon A Ñ m k b i) (Jacie A Ñ T p (m+i))⁻¹) k
lemma breeze.bearing {P Q:ℕ→ Coil F}{R S: Coil F}(p:∀ i≤e,breeze (fun j=>lineS (P j) i) (lineS R i))(q:∀ i≤e,breeze (fun j=>lineS (Q j) i) (lineS S i)): breeze (fun i=>lineS (P i*Q i) e) (lineS (R*S) e):=by simp only [line_mul]; exact breeze.sum (P:=fun n j=> lineS (P n) j.1*lineS (Q n) j.2) (S:=Finset.antidiagonal e) (fun j h=>by have he:= Finset.mem_antidiagonal.mp h; exact breeze.mul (p j.1 (by omega)) (q j.2 (by omega)))
lemma breeze.instep {P:ℕ→ℕ→ Coil F}{R:ℕ→ Coil F}(p:∀ j<k,∀ i≤e,breeze (fun n=>lineS (P n j) i) (lineS (R j) i)): breeze (fun n=> lineS (steepen (P n) k) e) (lineS (steepen R k) e):=by
   induction k generalizing e with
   | zero=> simp only [steepen]; exact breeze.const _
   | succ k ih=> simp only [steepen]; refine breeze.bearing (fun i h=> p k k.lt_succ_self i h) ?_; intro i hi; exact ih (fun j hj r hr=>p j (by omega) r (by omega))
lemma compassU (L:Theatre H T p e E W)(h:L.V.anchor≤m)(v:i≤e)(q:Bool) (k): breeze (fun n=>lineS (bindingS L.V.draws L.V.paid T p n m k q) i) (lineS (arrowV L.V.draws L.V.paid T p m k q) i):=by
    let R:=L.V
    apply breeze.instep (k:=k); intro j _ a u x y
    have h' : L.V.anchor≤ m+j:=by omega
    have hx l (t:l≤ a): Rising (fun n=>warp R.draws R.paid n m k q j) (beckon R.draws R.paid m k q j) l:=by cases q; exact destiny R h (by omega) _; exact hence R h' (by omega) _
    exact reelRise (e:=a) hx (P:=fun n=>warp R.draws R.paid n m k q j) (Q:=fun n=>(Jacob L.V.draws L.V.paid T p n (m+j))⁻¹ x y) (fun l b=>glim_inv L h' (b.trans (u.trans v)) x y)

-- cutoff quantitative. geometry exact fixed.
theorem distant (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W C':Credit)(v:i≤ e)(q:Bool): ∃ C:Credit,∀ S: CourseS H T p e E W C', let V:= S.vols; let P:= bindingS V.draws V.paid T p S.I.n S.spur S.length q; let Q:=arrowV V.draws V.paid T p S.spur S.length q; ∀ i' j:Alma F,twain (C.buy S.Age) S.cab (lineS P i i' j) (lineS Q i i' j):=by
    obtain ⟨Z,H⟩:= glacier H T p e E W C' q i v; refine ⟨Z,fun S=>?_⟩; intro V P Q i' j
    have hv n (h:S.I.b≤n): twain (Z.buy S.Age) S.cab (lineS P i i' j) (lineS (bindingS V.draws V.paid T p n S.spur S.length q) i i' j):= by
        exact H { S with I:= { S.I with N:=n, hg:=h}} i' j
    let f n:=lineS (bindingS V.draws V.paid T p n S.spur S.length q) i i' j; have ht:Tendsto f atTop (𝓝 (lineS Q i i' j)):= compassU S.robe.arch S.root v q S.length i' j
    exact ⟨(hv _ le_rfl).main, le_of_tendsto ht.norm ((eventually_ge_atTop S.I.b).mono fun n hn=> (hv n hn).side), le_of_tendsto (tendsto_const_nhds.sub ht).norm ((eventually_ge_atTop S.I.b).mono fun n hn=>(hv n hn).gap)⟩
end YM.WilsonCoeffUV.Cosmos
