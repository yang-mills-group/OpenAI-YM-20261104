import YM.WilsonCoeffUV.Root.UV.Distant
import YM.WilsonCoeffUV.Horizon.Lookup
import YM.WilsonCoeffUV.Product.Report.ReturnBase
/-!
# Spool compatibility, for every horizon in the Wilson branch

Before changing the field/stress convention. Exact engineering factor
*outside* reach-alphabet filters. This includes the entire formal product on
the stipulated tested geometry before older soft-stop. No k→∞. Matching
between canonical calibrations at different output horizons requires undoing
a matrix, not comparing nested physical outputs in this non-minimal basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Scopes
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Shard
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n f:Side}{U V:Type*}{r h D l e j k a N M m b i c q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{W:Frame G r}{Θ:Levels G}{T:ChartRatio G}{t:h ≤ r}{p:h<D}

def curtail (H: LabelsHold F W t)(X:Verse W): Verse F:=fun i=>X (climbC H i)
lemma opal_curve (p:h ≤ r)(I:LabelsHold F W p)(H:Hol G)(X:TowerS G D)(u:On k X): curtail I (opal W X)=opal F X:=by
   funext i; unfold curtail opal; ext n; rw [coeff_mk,coeff_mk, bridal I X.2 n i H (fun j r _ _=>⟨solo_mural u r j, solo_stretch u j r⟩)]
lemma opal_mu (F:Frame G h)(c:ℝ)(X:TowerS G D): opal F (c • X)=c • opal F X:=by
    funext i; unfold opal; rw [Pi.smul_apply]; ext1 n; rw [coeff_mk,Prod.smul_snd,glean_mu,coeff_smul,coeff_mk]
lemma ornate (Θ:Levels G)(T:ChartRatio G)(u:h≤ r)(X: TowerS G D): Spout Θ T N m h k X= (((Θ.S.block m).val:ℝ)^ (r-h))⁻¹ • Spout Θ T N m r k X:=by
    unfold Spout; rw [smul_smul]; congr 1
    unfold gradeH
    let w:=((ll Θ m).L.val:ℝ)
    have hp:0<w:=by unfold w; positivity
    have he:w^r=w^(r-h)*w^h:= by rw [←pow_add,Nat.sub_add_cancel u]
    change _= (w^_)⁻¹ * (w^r/w^k); rw [he, ← mul_div_assoc, ← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hp.ne'),one_mul]
lemma supp (hp:m<N)(g:G.Simple)(h:LocalRatio T)(X:TowerS G D)(t:On k X)(c:ℝ): Spout Θ T N m l k (c•X)= c • Spout Θ T N m l k X:=by
    have hx:= Shed_add Θ T (h:=l) (X:=fun _:Fin 1=>X) hp g h (fun _=>c) (fun _=>t); simpa only [Fintype.sum_unique] using hx
lemma registered (p:m+i≤N)(g:G.Simple)(v:LocalRatio T)(X: TowerS G D)(A:On k X)(d:ℝ): spools Θ T N k h m i (d • X)=d • spools Θ T N k h m i X:=by
    induction i generalizing X with
    | zero=> rfl
    | succ i ih=> rw [spools,spools,supp (by omega) g v X A]; exact ih (by omega) _ (ShedG Θ T (by omega) g v A le_rfl)
lemma spool_curve (p:m+i≤N)(g:G.Simple)(v:LocalRatio T)(z:h ≤ r)(X: TowerS G D)(A:On k X)(q:k≤l):
    spools Θ T N k h m i X = paceT Θ.S m (m+i)^(r-h) • spools Θ T N l r m i X:=by
   induction i generalizing X with
   | zero=> simp only [pace_self,Nat.add_zero,one_pow, one_smul]
            rfl
   | succ i ih=>
      let S:= Θ.S; let u:=(S.block (m+i)); let d:ℝ:= ((u.val:ℝ)^(r-h))⁻¹; have ht:m+i<N:=by omega
      let F:=Spout Θ T N (m+i) h k X; let Y:=Spout Θ T N (m+i) r l X
      have he:F=d•Y:=by unfold F; rw [ornate Θ T z, saturate Θ T ht g v A le_rfl q]
      have hx:= ih (by omega) F (ShedG Θ T ht g v A le_rfl); rw [spools,spools]; refine hx.trans ?_; rw [he];
      have hQ:On l Y:=On.expand (ShedG Θ T ht g v A q) q
      rw [registered (Θ:=Θ) (N:=N) (m:=m) (i:=i) (by omega) g v Y hQ d, smul_smul]; change (paceT Θ.S _ _ ^ _ *_) • _= _;
      congr 1
      have hz := pace_step S m (m+i)
      unfold d u; rw [show m+(i+1)=m+i+1 by omega,← hz,mul_pow, mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]

-- At h measured formulas return normalized vectors. Comparison with r matrices must lift
-- back to terminal calibration, not expect plain horizon restriction.
variable {Q: Fin (q+1)→SealR G} {T₁:SectionData F}{p':r<D}{T₂:SectionData W}
variable {X Z Q' V':Credit}

lemma wideH (pW:c≤ b)(g:G.Simple)(w:b ≤ m)(hp:m≤ N)(v:LocalRatio T)(H0:Hol G)(I:LabelsHold F W t)(φ:Wilt Q)(Y: Herit Q)
    (A:On k (AutumnDay Θ T φ Y m b N D))(L:Theatre H T₂ p' e X Z)(x:L.V.draws=Θ)(hv:L.V.paid=T)(ht:L.V.anchor ≤ c)(z:k ≤ l) :
    let r':= Reports Θ T T₂ p' φ Y m b c N l
    Reports Θ T T₁ p φ Y m b c N k = paceT Θ.S m b ^ h • steep Θ T T₁ p N c (m-c) (paceT Θ.S c b^(r-h) • curtail I (street Θ T T₂ p' N c (m-c) (((paceT Θ.S m b^r)⁻¹:ℝ) • r'))):=by
    intro o; let K:= AutumnDay Θ T φ Y m b N D; let u:= h
    let T':= Mer.spools Θ T N k u c (b-c) K; let X':= spools Θ T N l r c (b-c) K; let W':=opal W X'
    have hg : c+(b-c)=b:=Nat.add_sub_of_le pW; have he:T'= (paceT Θ.S c b)^(r-h) • X':= by
        unfold T' X' K; rw [spool_curve (p:=show c+(b-c)≤N by omega) g v t _ A z,hg]
    have hx: street Θ T T₂ p' N c (m-c) (((paceT Θ.S m b^r)⁻¹:ℝ) • o)= W':=by
        unfold o; rw [Reports, smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (pace_pos ..).ne'),one_smul];
        have hh:= Street_up (N:=N) (m:=c) (i:=m-c) L W' ht (by omega); rw [x,hv] at hh; exact hh
    rw [hx, opal_curve t I H0 X' (spoolEnd (by omega) g v (A.expand z)),Reports]; rw [show spools Θ T N k h c (b-c) (AutumnDay Θ T φ Y m b N D)=T' from rfl,he,opal_mu];
-- at fixed genes, actual reset relation may magnify powers from forward matrices.

def pha (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(m k:ℕ): Coil F:= hillcrest (fun i=> Chars F (towards A Ñ m i) (Jacie A Ñ T p (m+i))) k
lemma helm (L:Theatre H T₁ p e X Z)(h:L.V.anchor≤m)(v:i≤ e)(k): let S:=L.V
   breeze (fun n=>lineS (CurNames S.draws S.paid T₁ p n m k false) i) (lineS (pha S.draws S.paid T₁ p m k) i):=by
    intro S
    induction k generalizing i with
    | zero=> exact breeze.const _
    | succ k ih=>
       simp_rw [orchestra, pha,hillcrest]
       apply breeze.bearing (fun j p=>ih (by omega)); intro j t a b; have he: L.V.anchor ≤ m+k:=by omega
       exact reelRise (P:=fun n=>relativeF S.draws S.paid n m k) (Q:=fun n=> Jacob S.draws S.paid T₁ p n (m+k) a b) (fun i h'=> destiny L.V h (by omega) k) (fun i h=> matrix_glim L he (by omega) a b)

variable {V:ℕ→Verse F}{G': Verse F}
-- fixed m width convergence on both reports imported from reportUV (or other supplied convergence). no inverse-Growth claim on forward factors within this identity

def risingVerse (F:Frame G h)(V:ℕ→Verse F)(g:Verse F)(e:ℕ): Prop:= ∀ i,∀ j≤e,Rising (fun n=> V n i) (g i) j
lemma risePlay (A:ℕ→Cost)(b:Cost)(p:risingVerse F V G' e)(g:∀ j≤e,Rising A b j): risingVerse F (fun n=> music (A n) (V n)) (music b G') e:=by
    intro i j v; exact reelRise (P:=A) (Q:=fun n=> V n i) (fun a u=>g a (u.trans v)) (fun a u=>p i a (u.trans v))
lemma riseMat {H:ℕ→Coil F}{K:Coil F}(p:∀ j≤ e,breeze (fun n=>lineS (H n) j) (lineS K j))(g:risingVerse F V G' e) : risingVerse F (fun n=> H n *ᵥ V n) (K *ᵥ G') e:=by
    intro a i t; unfold Rising Matrix.mulVec dotProduct; simp_rw [map_sum,coeff_mul]; refine tendsto_finsetSum _ (fun j _=>tendsto_finsetSum _ (fun b h'=>?_)); have hx:= Finset.mem_antidiagonal.mp h'; exact Tendsto.mul (p b.1 (by omega) a j) (g j b.2 (by omega))
def hospice (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D) (m k:ℕ)(v:Verse F): Verse F:= pha A Ñ T p m k *ᵥ music (towards A Ñ m k) v
def elderX (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:h<D)(m k:ℕ)(v:Verse F): Verse F:= music (reveries A Ñ m k) (arrowV A Ñ T p m k false*ᵥ v)
lemma ascending (L:Theatre H T₁ p e X Z)(h:L.V.anchor≤m)(g:risingVerse F V G' e)(i): risingVerse F (fun n=> street L.V.draws L.V.paid T₁ p n m i (V n)) (hospice L.V.draws L.V.paid T₁ p m i G') e:=
   riseMat  (fun j v=>helm L h v i) (risePlay _ _ g (fun j v=> destiny L.V h (by omega) i))
lemma descending (L:Theatre H T₁ p e X Z)(h:L.V.anchor≤m)(g:risingVerse F V G' e)(i) : risingVerse F (fun n=> steep L.V.draws L.V.paid T₁ p n m i (V n)) (elderX L.V.draws L.V.paid T₁ p m i G') e:=
   risePlay _ _ (riseMat (fun j v=> compassU L h v false i) g) (fun j v=>hence L.V h (by omega) i)
lemma annoM (p:risingVerse F V G' e)(a:ℝ): risingVerse F (fun n=>a • V n) (a • G') e:= by
    intro i j v; unfold Rising; simp_rw [Pi.smul_apply,coeff_smul]; exact (p i j v).const_smul a

-- Includes any shipped products (individual convergences `reportUV`).
theorem restrictionStep (I:LabelsHold F W t)(pW:c≤ b)(w:b ≤ m) (φ:Wilt Q)
    (L:Theatre H T₂ p' e X Z)(M':Theatre H T₁ p e Q' V')(z:k ≤ l)
    (v:L.V.draws=Θ)(u:L.V.paid=T)(hv:L.V.anchor ≤ c)(x:M'.V.draws=Θ)(y:M'.V.paid=T)(g:M'.V.anchor ≤ c)
    (Y:ℕ→Herit Q)(hx:∀ᶠ n in atTop,On k (AutumnDay Θ T φ (Y n) m b n D)) (A:Verse F)(B:Verse W)
    (f:risingVerse F (fun n=> Reports Θ T T₁ p φ (Y n) m b c n k) A e)
    (f':risingVerse W (fun n=> Reports Θ T T₂ p' φ (Y n) m b c n l) B e) :
     let P:= paceT Θ.S m b
     ∀ j≤ e, ∀ i, coeff j (A i)=coeff j ((P^h • elderX Θ T T₁ p c (m-c) (paceT Θ.S c b^(r-h) • curtail I (hospice Θ T T₂ p' c (m-c) ((P^r)⁻¹ • B)))) i):=by
    intro P j d i
    let V(n:ℕ):=(P^r)⁻¹ • Reports Θ T T₂ p' φ (Y n) m b c n l
    let W':=(P^r)⁻¹ • B
    let T' (n):=curtail I (street Θ T T₂ p' n c (m-c) (V n)); let x':=curtail I (hospice Θ T T₂ p' c (m-c) W')
    have hu:= ascending L hv (show risingVerse W V W' e from annoM f' _) (m-c); rw [v,u] at hu
    have hp:risingVerse F T' x' e:= fun i=>hu (climbC I i)
    let Q (n):=P^h • steep Θ T T₁ p n c (m-c) (paceT Θ.S c b^(r-h) • T' n)
    have he:=descending M' g (annoM hp (paceT Θ.S c b^(r-h))) (m-c); rw [x,y] at he
    refine tendsto_nhds_unique (f i j d) ((annoM he (P^h) i j d).congr' ?_)
    filter_upwards [hx,eventually_ge_atTop m] with n hn he; exact congr_arg (fun Z:Verse F=>coeff j (Z i)) (wideH (T₁:=T₁) (p:=p) pW L.V.hG w he (u ▸ L.V.green) H I φ (Y n) hn L v u hv z).symm
end YM.WilsonCoeffUV.Mer.Scopes
