import YM.WilsonCoeffUV.Root.UV.Peaks
/-!
# Shear. Heads at earlier slots or orders. A must be absolute and not feed back via \sigma.
Rapt on inverse given by licence, not from EntryΔ. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V E:Type*}{r h D l j e k a N m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A B C x δ σ γ y:ℝ}

section sector
variable [AddCommGroup V][Module ℝ V]
def blockS (F:Frame G h)(l):= Finset.univ.filter fun i:Alma F=>valence F i=l
lemma vitae (v:Alma F): v∈blockS F l↔valence F v=l:=by simp [blockS]
-- right pull on SLOT
def troops (T: Wall F)(X: Alma F→V)(l) (j:Alma F):= ∑ i∈blockS F l,T i j • X i
lemma tramPost {T M:Wall F}(p:T*M=1)(h:Tram F 0 T)(e:Tram F 0 M)(X:Alma F→V)(v:Alma F)(hq:valence F v=l): troops M (troops T X l) l v=X v:=by
   have hp j (hj:j∈blockS F l):∑ i∈blockS F l, M i v*T j i=(1:Wall F) j v:=by
       rw [←p,Matrix.mul_apply]; simp_rw [show ∀ i,M i v*T j i=T j i*M i v from fun i=>mul_comm ..]; apply Finset.sum_subset (Finset.subset_univ _); intro a _ ha
       have hv:= (vitae j).mp hj; have h': valence F a≠l:= fun x=>ha ((vitae a).mpr x); rcases lt_or_gt_of_ne h' with c|c; · rw [h j a (by omega),zero_mul]
       rw [e a v (by omega),mul_zero]
   simp_rw [troops, Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]; simp_rw [←Finset.sum_smul]
   rw [Finset.sum_eq_single v]; · rw [hp v ((vitae ..).mpr hq),Matrix.one_apply_eq,one_smul]
   intro b hb hu; rw [hp b hb,Matrix.one_apply_ne hu,zero_smul]; exact fun h=>False.elim (h ((vitae ..).mpr hq))
-- everything but troops. by if on indices
def camps (T:Coil F)(P:BookC F V E)(l e r:ℕ)(j:Alma F): Ten V E r:= ∑ i,∑ w∈ Finset.antidiagonal e, if valence F i=l ∧ w.1=0 then 0 else lineS T w.1 i j • P i w.2 r
lemma campPost (P:BookC F V E)(T:Coil F)(l e r:ℕ)(j:Alma F): troops (lineS T 0) (fun i=> P i e r) l j=impose P T j e r-camps T P l e r j:=by
   simp_rw [camps,impose, Finset.sum_apply,affix, Finset.sum_apply,Pi.smul_apply,← Finset.sum_sub_distrib]; rw [troops,blockS,Finset.sum_filter]; refine Finset.sum_congr rfl fun i _=>?_; by_cases g: valence F i=l
   · rw [if_pos g]; rw [Finset.sum_eq_single (0,e)]; · simp only [g, true_and,if_true,lineS,Matrix.of_apply,sub_zero]
     intro b hb ht; have hx:=Finset.mem_antidiagonal.mp hb; rw [if_neg]; · unfold lineS; simp
     exact fun ⟨_,h⟩=> ht (Prod.ext h (show b.2=e from by omega)); simp
   simp [g,lineS]
end sector
lemma troopsStow {X:Alma F→ChamberTen G (Vote D) r}(T: Wall F)(e:∀ i: Alma F,valence F i=l → Twig 0 s A (troops T X l i))(h:leaseM n F T)(p:Rapt F (steed T n) C)(j:Alma F)(v:valence F j=l): Twig 0 s (((blockS F l).card:ℝ)*(C*A)) (X j):=by
    have hc:=tramPost (recognition h) h.1 (steed_value h ▸ Tram.elastic h) X j v
    rw [← show ∑ i∈blockS F l,C*A=((blockS F l).card:ℝ)*(C*A) from by simp]
    exact hc ▸ Cork.sum (P:=fun i=> steed T n i j • troops T X l i) (fun i hi=>let hx:= (vitae i).mp hi; Cork.cost (Cork.μ (e _ hx) _) (mul_le_mul_of_nonneg_right (show |steed T n i j|≤C from p.2 i j (hx.trans v.symm)) (e j v).1))

structure CostS (T X:Coil F)(c k r:ℕ)(A θ:ℝ): Prop where
    spent i j m: valence F j=c→ (m<k∨m=k∧r≤valence F i) → twain A θ (lineS T m i j) (lineS X m i j)
def cPrice (F:Frame G h)(k:ℕ)(A B:ℝ):=∑ _ : Alma F,∑ _ ∈ Finset.antidiagonal k,2*A*B
lemma campPay {P Q: Thesis F D}{T X:Coil F}(p:Tram F 0 (lineS T 0))(q:Tram F 0 (lineS X 0))(g:CostS T X l k r B σ)(he:∀ i,shellK (valence F i) (P i))(hp:∀ i,shellK (valence F i) (Q i))(u:0≤ A)(v:0≤B)(w:0≤σ)
    (hy:∀ i: Alma F,∀ j:ℕ, j<k∨ j=k ∧ valence F i<l→Shelf Bank.terrain 0 s A σ (P i j r) (Q i j r)) (j: Alma F)(hh:valence F j=l): Shelf Bank.terrain 0 s (cPrice F k A B) σ (camps T P l k r j) (camps X Q l k r j):=by
    have hZ: Shelf Bank.terrain 0 s (2*A*B) σ (0:ChamberTen G (Vote D) r) 0:= Shelf.zero.step (by positivity) w
    refine Shelf.sum (fun i _=>Shelf.sum (fun z hz=>?_)); change Shelf _ _ _ _ _ (if _ then _ else _) (if _ then _ else _);
    by_cases hm:valence F i=l ∧ z.1=0
    · simp only [if_pos hm]; exact hZ
    rw [if_neg hm,if_neg hm]; have ht:=Finset.mem_antidiagonal.mp hz
    by_cases hv: valence F i+z.2<r
    · rw [he i z.2 r hv,hp i z.2 r hv,smul_zero,smul_zero]; exact hZ
    by_cases hx: z.2<k ∨ z.2=k∧ valence F i<l
    · exact Shelf.mag (hy _ _ hx) (g.spent i j z.1 hh (by omega))
    rw [show z.1=0 by omega,p i j (by omega),q i j (by omega),zero_smul,zero_smul]; exact hZ

lemma sector_minus [AddCommGroup V][Module ℝ V](X:Alma F→V)(T M:Wall F)(j:Alma F): troops T X l j - troops M X l j= troops (T-M) X l j:=by unfold troops; simp_rw [Matrix.sub_apply, sub_smul,Finset.sum_sub_distrib]
lemma sector_diff [AddCommGroup V][Module ℝ V](X P: Alma F→ V)(T:Wall F)(j: Alma F): troops T X l j - troops T P l j= troops T (X-P) l j:=by unfold troops; simp_rw [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]
lemma costScuff {P Q:Coil F}(p:CostS P Q l k r B σ)(g:r≤ l+k)(X:Alma F→ChamberTen G (Vote D) r)(h:∀ i,valence F i=l→Twig 0 s x (X i))(j:Alma F)(hj:valence F j=l) : Twig 0 s (((blockS F l).card:ℝ)*(B*σ*x)) (troops (lineS P 0-lineS Q 0) X l j):=by
    unfold troops; rw [←show ∑ _∈blockS F l, B*σ*x=((blockS F l).card:ℝ)*(B*σ*x) from by simp]; refine Cork.sum (fun i ht=>?_); have hh:= (vitae ..).mp ht; have hv:= p.spent i j 0 hj (by omega)
    rw [Matrix.sub_apply]; exact Cork.cost (Cork.μ (h _ hh) _) (mul_le_mul_of_nonneg_right (show |_|≤_ from hv.gap) (h _ hh).1)
end YM.WilsonCoeffUV.Cosmos
