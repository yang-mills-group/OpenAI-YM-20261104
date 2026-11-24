import YM.WilsonCoeffUV.Root.UV.RebaseBound
/-!
# Only finitely many strict events. Multiplicities of positions charged by telescoping n².
Damping without price, delta leading needed to suppress Lipschitz factor repeated.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q n':ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' x A B C δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}
-- forward chain M0: u*w_d, stable inverse in increasing level on LEFT. cost sup.
lemma toll_unchanged (v:twain A δ t t')(h: ‖x‖≤1)(_ha:0≤δ) : twain A δ (x*t) (x*t'):= by
    refine ⟨(by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) h).trans v.main), (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) h).trans v.side),?_⟩
    rw [← mul_sub, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) h).trans v.gap

noncomputable def steepen (T:ℕ→ Coil F):ℕ→ Coil F
    | 0 => 1
    | i+1=> T i * steepen T i
noncomputable def hillcrest (T:ℕ→ Coil F):ℕ→ Coil F
    | 0 => 1
    | i+1=> hillcrest T i * T i
lemma campsE (A B:ℕ→ Coil F)(h:∀ j<n', IsUnit (A j).det)(p:∀ j<n', B j=(A j)⁻¹): IsUnit (hillcrest A n').det ∧ steepen B n'=(hillcrest A n')⁻¹ :=by
   induction n' with
   | zero=>simp [hillcrest,steepen]
   | succ i ih=>
      obtain ⟨t,v⟩:=ih (fun j q=> h j (by omega)) (fun j q=> p j (by omega)); let C:=hillcrest A i; have hx:=h i (by omega)
      rw [steepen,hillcrest,v,p i (by omega)]; refine ⟨by rw [Matrix.det_mul]; exact t.mul hx,Eq.symm (Matrix.inv_eq_right_inv ?_)⟩; rw [← Matrix.mul_assoc (C*A i), Matrix.mul_assoc C, Matrix.mul_nonsing_inv (A i) hx,_root_.mul_one, Matrix.mul_nonsing_inv _ t]

def mince (P Q: Coil F)(e:ℕ)(j k:Alma F):ℝ := ∑ i∈ houseD e,(lineS P i.1*lineS Q i.2) j k + ∑ v∈ Finset.univ.erase j,lineS P 0 j v* lineS Q e v k
lemma famed (P Q:Coil F)(e:ℕ)(j k:Alma F): lineS (P*Q) e j k=lineS P 0 j j*lineS Q e j k + mince P Q e j k:=by
   rw [line_mul,← Finset.add_sum_erase _ _ (show (0,e)∈ Finset.antidiagonal e from Finset.mem_antidiagonal.mpr (by omega)), Matrix.add_apply, Matrix.mul_apply, ← Finset.add_sum_erase Finset.univ (fun v=>lineS P (0,e).1 j v * lineS Q (0,e).2 v k) (Finset.mem_univ j),Matrix.sum_apply]; unfold mince houseD; ac_rfl
section
variable {x θ:U→ℝ}{P Q: U→ℕ→ Coil F}{d:U→ℕ}
structure swan (F:Frame G h)(P Q:Wall F):Prop where
    step i j: i≠j → highUp F i ≤ highUp F j → P i j=0
    stump i j:i≠j → highUp F i≤highUp F j→Q i j=0
    toe i:P i i= Q i i
    slip i:‖P i i‖≤1
lemma saddleSwan {P Q:Coil F}(p:leaseM n F (lineS P 0))(q:leaseM n F (lineS Q 0))(A B:Cost): swan F (lineS (Chars F A P⁻¹) 0) (lineS (Chars F B Q⁻¹) 0):=by
    rw [maxStroke,maxStroke]; refine ⟨fun i j v t=>(quiet p i j t).trans (if_neg v),fun i j v t=>(quiet q i j t).trans (if_neg v),fun i=>(quiet p i i le_rfl).trans (quiet q i i le_rfl).symm, fun i=> eased p i⟩

abbrev twinge (d:U→ℕ)(P:U→ℕ→ Coil F)(i:Jag d): Coil F:= P i.cargo i.coin
abbrev stairs (d:U→ℕ)(P:U→ℕ→ Coil F)(i: Portago d):=steepen (P i.cargo) i.coin
abbrev Piers (F:Frame G h)(x θ:U→ℝ)(P Q:U→Coil F)(e:ℕ)(j k:Alma F):Prop:= clips x θ (fun i=> lineS (P i) e j k) (fun i=>lineS (Q i) e j k)
def priorW {d:U→ℕ}(i: Jag d): Portago d:=⟨i.cargo,i.coin,i.credit.le⟩
lemma cropsU {a' b': Alma F}(p:Piers F (rubP d x) (rubP d θ) (stairs d P) (stairs d Q) e a' b'): Piers F (Bank.rub d x) (Bank.rub d θ) (fun i=>steepen (P i.cargo) i.coin) (fun i=> steepen (Q i.cargo) i.coin) e a' b':=by obtain ⟨D,C,h,e⟩:= p; exact ⟨D,C,h,fun i=>e (priorW i)⟩
lemma mint_cost (h:Brite x θ)(j k:Alma F)(Pp:∀ a:Jag d,swan F (lineS (twinge d P a) 0) (lineS (twinge d Q a) 0))(hz:∀ i ≤ e, CreditsS (Bank.rub d x) (Bank.rub d θ) (fun a=>lineS (twinge d P a) i) (fun a=>lineS (twinge d Q a) i))(hp:∀ i<e,CreditsS (rubP d x) (rubP d θ) (fun a=>lineS (stairs d P a) i) (fun a=>lineS (stairs d Q a) i)) (hq:∀ i: Alma F,highUp F i<highUp F j → Piers F (rubP d x) (rubP d θ) (stairs d P) (stairs d Q) e i k):
   clips (Bank.rub d x) (Bank.rub d θ) (fun i=> mince (twinge d P i) (stairs d P (priorW i)) e j k) (fun i=> mince (twinge d Q i) (stairs d Q (priorW i)) e j k):= by
    have ht:Brite (Bank.rub d x) (Bank.rub d θ):= ⟨fun i=>h.large _,fun i=> h.dist _⟩
    unfold mince; refine clips.add ?_ ?_ ht
    · apply clips.sum ht; intro i hi; refine (CreditsS.prod (hz i.1 (houseJ hi).1) ?_ ht) j k; exact fun j k=> cropsU (hp _ (houseJ hi).2 j k)
    apply clips.sum ht; intro i hi; by_cases hh:highUp F i< highUp F j
    · exact (hz 0 (by omega) j i).mul (cropsU (hq i hh))
    have hu : j≠ i:= Ne.symm (Finset.mem_erase.mp hi).1
    simp_rw [fun i'=> (Pp i').step _ _ hu (by omega),fun i'=>(Pp i').stump _ _ hu (by omega),zero_mul]; exact clips.one ht _
lemma loftF (h:Brite x θ)(r k: Alma F)(hb:∀ n,(d n:ℝ)≤ x n)(p:∀ i:Jag d,swan F (lineS (twinge d P i) 0) (lineS (twinge d Q i) 0))(hz: clips (Bank.rub d x) (Bank.rub d θ) (fun i=> mince (twinge d P i) (stairs d P (priorW i)) e r k) (fun i=> mince (twinge d Q i) (stairs d Q (priorW i)) e r k)): Piers F (rubP d x) (rubP d θ) (stairs d P) (stairs d Q) e r k:=by
   obtain ⟨c,C,a,hq⟩:=hz; let t:= lineS (1:Coil F) e r k; let T:=‖t‖; refine ⟨c+1,T+C,by positivity,fun ⟨v,m,g⟩=>?_⟩
   have he:∀ i≤m,twain (T+i*(C*(x v)^c)) (θ v) (lineS (steepen (P v) i) e r k) (lineS (steepen (Q v) i) e r k):=by
      intro i
      induction i with
      | zero=> intro _; simp only [Nat.cast_zero, zero_mul,add_zero,steepen]; exact twain.one _ _ (h.dist _) le_rfl
      | succ i ih=>
         intro w; rw [steepen,steepen,famed,famed]; let u:Jag d:= ⟨v,i,by omega⟩; rw [← show lineS (P v i) 0 r r=lineS (Q v i) 0 r r from (p u).toe r]; push_cast; rw [add_mul,one_mul, ←add_assoc]; exact (toll_unchanged (ih (by omega)) ((p u).slip r) (h.dist _)).add (hq u)
   have hh:=h.large v; refine (he m le_rfl).lift ?_ (h.dist _); change T+m*(C*x v^c)≤(T+C)*x v^(c+1); rw [add_mul]; apply add_le_add (le_mul_of_one_le_right (norm_nonneg t) (one_le_pow₀ hh)); rw [pow_succ,←mul_assoc C,mul_comm (m:ℝ)]; exact mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr g).trans (hb _)) (by positivity)
-- solve lex via charge steps, no sums induct aggregate.
theorem baron (hB:Brite x θ)(hb:∀ n,(d n:ℝ)≤ x n)(K:∀ i≤e,CreditsS (Bank.rub d x) (Bank.rub d θ) (fun a=>lineS (twinge d P a) i) (fun a=>lineS (twinge d Q a) i))(hp:∀ i: Jag d,swan F (lineS (twinge d P i) 0) (lineS (twinge d Q i) 0)): CreditsS (rubP d x) (rubP d θ) (fun i=>lineS (stairs d P i) e) (fun i=>lineS (stairs d Q i) e):=by
    induction e using Nat.strong_induction_on with
    | h e ih=>
       have hz j (p:j<e):CreditsS (rubP d x) (rubP d θ) (fun i=>lineS (stairs d P i) j) (fun i=>lineS (stairs d Q i) j):= ih _ p (fun i hi=> K i (hi.trans p.le))
       intro i j
       have ht n : ∀ v, highUp F v<n → Piers F (rubP d x) (rubP d θ) (stairs d P) (stairs d Q) e v j:=by
          induction n with
          | zero=> intro i p; omega
          | succ n ih=> exact fun v w=> loftF hB v j hb hp (mint_cost hB v j hp K hz (fun i p=> ih i (by omega)))
       exact ht _ _ (high_lt i)
end
end YM.WilsonCoeffUV.Cosmos
