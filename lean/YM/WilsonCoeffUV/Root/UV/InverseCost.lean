import YM.WilsonCoeffUV.Root.UV.WindowPurse
/-!
# Inverse transfer matrices at fixed-pair port. Finite-form limits and orientations. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}
section
variable {x θ:U → ℝ}{P Q Y Z:U→ Wall F}
def CreditsS (x θ:U → ℝ)(P Q:U→ Wall F):Prop:= ∀ i j: Alma F,clips x θ (fun n=> P n i j) (fun n=> Q n i j)
lemma CreditsS.fixed (h:Brite x θ)(P: Wall F) : CreditsS x θ (fun _=>P) (fun _=>P):= fun i j=> clips.one h (P i j)
lemma CreditsS.add (p:CreditsS x θ P Q)(q:CreditsS x θ Y Z)(h:Brite x θ): CreditsS x θ (fun n=>P n+Y n) (fun n=>Q n+Z n):=fun i j=> (p i j).add (q i j) h
lemma CreditsS.sub (p:CreditsS x θ P Q)(q:CreditsS x θ Y Z)(h:Brite x θ): CreditsS x θ (fun n=>P n-Y n) (fun n=>Q n-Z n):=fun i j=> (p i j).sub (q i j) h
lemma CreditsS.neg (p:CreditsS x θ P Q): CreditsS x θ (fun n=> -(P n)) (fun n=> -(Q n)):=fun i j=> (p i j).neg
lemma CreditsS.prod (p:CreditsS x θ P Q)(q:CreditsS x θ Y Z)(h:Brite x θ): CreditsS x θ (fun n=> P n*Y n) (fun n=> Q n*Z n):=by
    intro i j; simp only [Matrix.mul_apply]; exact clips.sum h (fun k _=>(p i k).mul (q k j))
lemma CreditsS.sum {S:Finset α}{P Q:U→ α → Wall F}(h:∀ i∈ S,CreditsS x θ (fun n=> P n i) (fun n=> Q n i))(e:Brite x θ): CreditsS x θ (fun n=>∑ i∈S,P n i) (fun n=>∑ i∈ S,Q n i):= by intro i j; simp only [Matrix.sum_apply]; exact clips.sum e fun k h'=> h k h' i j
lemma CreditsS.pow (p:CreditsS x θ P Q)(h:Brite x θ)(i:ℕ): CreditsS x θ (fun n=>P n^i) (fun n=> Q n^i):=by
    induction i with
    | zero=> simp only [pow_zero]; exact fixed h 1
    | succ i ih=> simp_rw [pow_succ]; exact ih.prod p h
lemma CreditsS.ride {L:U→ Side}(p:CreditsS x θ P Q)(h:Brite x θ): CreditsS x θ (fun i=> steed (P i) (L i)) (fun i=>steed (Q i) (L i)) := by
   let W i:= saddle (L i) F
   have hv : CreditsS x θ W W:=by
       intro i j; refine ⟨0,1,zero_le_one,fun v=>?_⟩; rw [pow_zero,mul_one]; refine twain.one _ _ (h.dist v) ?_
       by_cases t:i=j; · subst j; unfold W saddle; dsimp only; rw [Matrix.diagonal_apply_eq,Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (matPow₁ ..)))]; exact inv_le_one_of_one_le₀ (matPow₁ ..)
       simp [W,saddle,t]
   exact hv.prod (CreditsS.sum (S:=Finset.range (ceiling _)) (fun i _ => ((fixed h 1).sub (p.prod hv h) h).pow h i) h) h
-- no polynomial residue in higher from unbounded lower support
abbrev houseD (i:ℕ):=(Finset.antidiagonal i).erase (0,i)
lemma dimneg {i:ℕ}(h:0< i){P:Coil F}(u:leaseM n F (lineS P 0)): lineS (P⁻¹) i = (steed (lineS P 0) n)* -(∑ j∈ houseD i,lineS P j.1*lineS P⁻¹ j.2):=by
    let Q:= lineS P 0; let V:= ∑ j∈houseD i,lineS P j.1* lineS P⁻¹ j.2
    have H : lineS (P*P⁻¹) i=0:=by rw [Matrix.mul_nonsing_inv P (stellarized u)]; exact choral F _ h
    rw [line_mul,← Finset.add_sum_erase _ _ (show (0,i)∈ Finset.antidiagonal i from Finset.mem_antidiagonal.mpr (by simp))] at H
    rw [← steed_value u]; change _=Q⁻¹ * (-V); rw [← show Q*lineS P⁻¹ i=-V from eq_neg_of_add_eq_zero_left H, ←Matrix.mul_assoc,nonsing_inv_mul Q (trove u),_root_.one_mul]
lemma houseJ {j:ℕ×ℕ}(e:j∈houseD i): j.1≤ i∧j.2< i:=by
    obtain ⟨u,v⟩:= Finset.mem_erase.mp e; have he:= Finset.mem_antidiagonal.mp v; refine ⟨by omega,?_⟩; by_contra! p; exact u (Prod.ext (show j.1=0 from by omega) (show j.2=i from by omega))
lemma CreditsS.pony {P Q:U→ Coil F}(p:∀ j≤ i,CreditsS x θ (fun n=>lineS (P n) j) (fun n=> lineS (Q n) j))(h:Brite x θ){L:U→Side}(q:∀ i,leaseM (L i) F (lineS (P i) 0))(g:∀ i,leaseM (L i) F (lineS (Q i) 0)): CreditsS x θ (fun n=>lineS (P n)⁻¹ i) (fun n=> lineS (Q n)⁻¹ i):= by
    induction i using Nat.strong_induction_on with
    | h i ih=>
       by_cases e:i=0; · subst i; simp_rw [fun i=> line_steed (q i),fun i=>line_steed (g i)]; exact (p 0 (le_refl _)).ride h
       simp_rw [fun v=> dimneg (show 0< i by omega) (q v),fun v=> dimneg (show 0< i by omega) (g v)]; exact ((p 0 (by omega)).ride h).prod ((CreditsS.sum (fun j v=> ((p j.1 (houseJ v).1).prod (ih j.2 (houseJ v).2 (fun i u=>p i (u.trans (houseJ v).2.le))) h)) h).neg) h
end
section
variable {P Q Y Z:ℕ→ Wall F}{A B C D: Wall F}
def breeze (P:ℕ→Wall F)(Q:Wall F):Prop:= ∀ i j:Alma F,Tendsto (fun n=>P n i j) atTop (𝓝 (Q i j))
lemma breeze.const (p: Wall F): breeze (fun _=>p) p:= fun _ _=> tendsto_const_nhds
lemma breeze.neg (h:breeze P A):breeze (fun i=> -(P i)) (-A):=fun i j=> (h i j).neg
lemma breeze.sub (h:breeze P A)(p:breeze Q B): breeze (fun i=> P i-Q i) (A-B) := fun i j => (h i j).sub (p i j)
lemma breeze.mul (h:breeze P A)(p:breeze Q B): breeze (fun i=>P i*Q i) (A*B):=by intro i j; simp only [Matrix.mul_apply]; exact tendsto_finsetSum _ (fun k _=>(h i k).mul (p k j))
lemma breeze.pow (h:breeze P A)(i:ℕ): breeze (fun n=> P n^i) (A^i):=by induction i with
                                                                           | zero=>simp only [pow_zero]; exact const 1
                                                                           | succ i ih=>simp_rw [pow_succ]; exact ih.mul h
lemma breeze.sum {S:Finset U}{P:ℕ→U→ Wall F}{Q:U→ Wall F}(p:∀ i∈ S,breeze (fun n=> P n i) (Q i)):breeze (fun n=> ∑ i∈S,P n i) (∑ i∈ S,Q i):=by intro i j; simp only [Matrix.sum_apply]; exact tendsto_finsetSum _ (fun u v=> p u v i j)
lemma breeze.route (P:ℕ→ Coil F)(V:Coil F)(u:∀ j≤ k,breeze (fun n=> lineS (P n) j) (lineS V j))(v:∀ᶠ i:ℕ in atTop,leaseM n F (lineS (P i) 0))(q:leaseM n F (lineS V 0)):
    breeze (fun n=> lineS (P n)⁻¹ k) (lineS V⁻¹ k):=by
    induction k using Nat.strong_induction_on with
    | h k ih=>
       have hv: breeze (fun i=> steed (lineS (P i) 0) n) (steed (lineS V 0) n):= (breeze.const (saddle n F)).mul (breeze.sum (S:=Finset.range (ceiling h)) (fun i _=> ((breeze.const 1).sub ((u 0 (by omega)).mul (breeze.const (saddle n F)))).pow i))
       intro i j
       by_cases g:k=0
       · subst k; simp_rw [line_steed q]; exact (hv i j).congr' (v.mono (fun s vs=> congr_arg (fun V:Wall F=> V i j) (line_steed vs).symm))
       have ht:= (hv.mul ((breeze.sum (fun j (v:j∈houseD k)=> breeze.mul (u _ (houseJ v).1) (ih _ (houseJ v).2 (fun i h=> u i (h.trans (houseJ v).2.le))))).neg)) i j
       rw [dimneg (show 0<k from by omega) q]; exact ht.congr' (v.mono fun x vx=> congr_arg (fun V:Wall F=> V i j) (dimneg (show 0<k from by omega) vx).symm)
end
variable {C':Credit}(L:Theatre H T p e E W)
lemma glim_inv (u:L.V.anchor≤m)(p':i≤ e)(a b: Alma F): Tendsto (fun n=>lineS (Jacob L.V.draws L.V.paid T p n m)⁻¹ i a b) atTop (𝓝 (lineS (Jacie L.V.draws L.V.paid T p m)⁻¹ i a b)):= breeze.route (fun n=> Jacob L.V.draws L.V.paid T p n m) _ (fun _ hi=>matrix_glim L u (hi.trans p')) ((eventually_gt_atTop m).mono (fun _ hn=> leaseN L u hn)) (leaseOld L u) a b
end YM.WilsonCoeffUV.Cosmos
