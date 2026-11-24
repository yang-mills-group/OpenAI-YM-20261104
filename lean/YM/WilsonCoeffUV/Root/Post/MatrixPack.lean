import YM.WilsonCoeffUV.Root.Post.Inverse
/-! # Full column tapes. Right action with charged truncated order. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}

abbrev BookC (F:Frame G h)(V α:Type*) := Alma F → Pal V α
-- constructed once; playback linear
section generic
variable [AddCommGroup V][Module ℝ V]
def affix (A: Blue.Cost)(v:Pal V U): Pal V U := fun i=> ∑ j∈Finset.antidiagonal i, coeff j.1 A • v j.2
def impose (P: BookC F V U)(A:Coil F): BookC F V U:=fun i=> ∑ j, affix (A j i) (P j)
lemma affix_sum {X:Type*}(A: Finset X)(V: X→ Pal V U)(a:Blue.Cost): affix a (∑ x∈A,V x)=∑ x∈A,affix a (V x):=by
   ext1 i; rw [Finset.sum_apply]; simp_rw [affix,Finset.sum_apply,Finset.smul_sum]; exact Finset.sum_comm
lemma addend (A:Finset E)(v: E→Blue.Cost)(p:Pal V U): affix (∑ i∈ A,v i) p=∑ i∈A,affix (v i) p:=by
   ext1 i; rw [Finset.sum_apply]; simp_rw [affix,map_sum,Finset.sum_smul]; exact Finset.sum_comm
lemma triangle {X:Type*}[AddCommMonoid X] (p:ℕ→ℕ→ℕ→X)(n): (∑ i∈Finset.antidiagonal n,∑ j∈ Finset.antidiagonal i.1,p j.1 j.2 i.2) =∑ i∈ Finset.antidiagonal n,∑ j∈ Finset.antidiagonal i.2,p i.1 j.1 j.2:=by
    rw [Finset.sum_sigma', Finset.sum_sigma'];
    let S: (ℕ×ℕ)→Finset (ℕ×ℕ):= fun i=>Finset.antidiagonal i.1; let T: (ℕ×ℕ)→Finset (ℕ×ℕ):= fun i=>Finset.antidiagonal i.2
    let I:= Sigma (fun _ : ℕ×ℕ => ℕ×ℕ)
    let F (i:I): I:= ⟨(i.2.1,i.2.2+i.1.2),(i.2.2,i.1.2)⟩; let G (i:I): I:= ⟨(i.1.1+i.2.1,i.2.2),(i.1.1,i.2.1)⟩
    let A:= (Finset.antidiagonal n).sigma S; let B:= (Finset.antidiagonal n).sigma T
    have hh i (h:i∈ A): G (F i)=i∧F i∈B:=by
       obtain ⟨⟨a,b⟩,c,d⟩:=i; simp [A,S] at h; simp [F,G,B,T]; exact ⟨by rw [h.2],Finset.mem_sigma.mpr ⟨Finset.mem_antidiagonal.mpr (show c+(d+b)=n from by omega),Finset.mem_antidiagonal.mpr rfl⟩⟩
    have ht i (h:i∈ B): F (G i)=i∧G i∈ A:=by
       obtain ⟨⟨a,b⟩,c,d⟩:=i; simp [B,T] at h; simp [F,G,A,S]; exact ⟨by rw [h.2],Finset.mem_sigma.mpr ⟨Finset.mem_antidiagonal.mpr (show a+c+d=n from by omega),Finset.mem_antidiagonal.mpr rfl⟩⟩
    exact Finset.sum_bij (fun i _=> F i) (fun i h=>(hh i h).2) (fun i h j v e=> ((hh i h).1.symm.trans (congr_arg G e)).trans (hh j v).1) (fun i h=>⟨G i,(ht i h).2,(ht i h).1⟩) (fun _ _=>rfl)
lemma affix_mul (a b:Blue.Cost)(v:Pal V U): affix a (affix b v)=affix (a*b) v:=by
    ext1 i; simp_rw [affix,coeff_mul, Finset.smul_sum, Finset.sum_smul,smul_smul]; exact (triangle (fun j s t=> (coeff j a*coeff s b) • v t) i).symm
lemma imposition (A B:Coil F)(T:BookC F V U): impose (impose T A) B=impose T (A*B):=by
    ext1 k; simp_rw [impose,affix_sum, affix_mul,Matrix.mul_apply,addend, mul_comm]; exact Finset.sum_comm
lemma no_tariff (P:Pal V U): affix 0 P=0:=by ext1 i; simp [affix]
lemma noslip (A:Blue.Cost) : affix A (0:Pal V U)=0:=by ext1 i; simp [affix]
lemma purePayment (P:Pal V U)(x:ℝ): affix (PowerSeries.C x) P=x • P:=by
    ext1 i; unfold affix; rw [Finset.sum_eq_single (0,i)]; · simp
    intro b hb hu; have he:= Finset.mem_antidiagonal.mp hb; have hx:b.1≠0:= fun h=>hu (Prod.ext h (show b.2=i from by omega))
    rw [coeff_C_of_ne_zero hx,zero_smul]
    simp
lemma affix_plain (p:Pal V U): affix 1 p=p:=by rw [←map_one (PowerSeries.C (R:=ℝ)), purePayment,one_smul]
lemma impose_plain (P:BookC F V U): impose P 1=P:=by
   ext1 i; unfold impose; rw [Finset.sum_eq_single i]; · rw [Matrix.one_apply_eq,affix_plain]
   intro b _ hb; rw [Matrix.one_apply_ne hb,no_tariff]; simp
lemma impose_billed (A:Coil F)(p:trample F A)(P:BookC F V U)(h:∀ i,shellK (valence F i) (P i))(j):shellK (valence F j) (impose P A j):=by
    intro e r t; unfold impose; simp_rw [Finset.sum_apply,affix,Finset.sum_apply,Pi.smul_apply]; apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro v hv; by_cases hR: valence F i≤ valence F j+v.1
    · have hg:= Finset.mem_antidiagonal.mp hv; rw [h i v.2 r (by omega),smul_zero]
    rw [show coeff v.1 (A i j)=0 from p v.1 i j (by omega),zero_smul]
lemma aspire (a:Blue.Cost)(P:Pal V U)(p:∀ k,Pure (P k))(i): Pure (affix a P i):=by intro r; rw [affix,Finset.sum_apply]; exact Blue.Smooth.sum fun j _=> (p j.2 r).smul _
lemma impose_smooth (A:Coil F)(P:BookC F V U)(p:∀ i r,Pure (P i r))(i r): Pure (impose P A i r):=by intro j; simp_rw [impose,Finset.sum_apply]; exact Blue.Smooth.sum fun k _=> aspire (A k i) (P k) (p k) r j
lemma affix_shell (A:Blue.Cost)(p:Pal V U)(h:shellK k p): shellK k (affix A p):=by
    intro i r q; rw [affix,Finset.sum_apply]; apply Finset.sum_eq_zero; intro j hj; have he:= Finset.mem_antidiagonal.mp hj; rw [Pi.smul_apply,h j.2 _ (by omega),smul_zero]
end generic
-- finite flash and Wreathe
lemma sponsor {U:Type}[Fintype U] (p:Pal ℝ U)(A:Blue.Cost)(h:shellK k p): flash (affix A p)=Blue.soil (U:=U) A * flash p:=by
    ext1 i; rw [flash,coeff_mk,coeff_mul,affix,visible_sum _];
    · apply Finset.sum_congr rfl; intro j _; rw [visible_μ (finite_shell h _) _,Blue.soil,coeff_map,flash,coeff_mk]; rw [Algebra.smul_def]; rfl
    exact fun _ _=> finite_μ (finite_shell h _) _
lemma incense (A:Blue.Cost)(p q:Vell G n D)(s:Signed)(h:shellK l p)(e:shellK k q)(x:Wreathe p q s): Wreathe (affix A p) (affix A q) s:=by
   have H (Y:Vell G n D)(v:Volume D): jot v (affix A Y)= affix A (jot v Y):=by ext i r x; rw [jot_here]; unfold affix; simp_rw [Finset.sum_apply,Pi.smul_apply,_root_.sum_apply,_root_.smul_apply,jot_here]
   intro v Z I x' X X' ht; rw [H,H,sponsor _ A (jot_length v e), sponsor _ A (jot_length _ h),map_mul,map_mul,income,income, x v ht]
end YM.WilsonCoeffUV.Cosmos
