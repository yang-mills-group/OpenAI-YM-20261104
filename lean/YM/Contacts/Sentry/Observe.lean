import YM.Next.UV_STRESS.Shell
import YM.Contacts.Costar.Ticket
/-!
Arbitrary finite index for local words, companions read the quotient fields
of the single unselected system; allow both reindexing choices and nested
decompositions without changing the separated kernel. All valuations on these
arrays will work for general heterogeneous fields rather than choosing identical
horizons for unrelated clusters. Symmetry invoked always away from Conf.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter Extraction Table Ward
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge} {L:Register G}{C:Family G}
variable {ι J : Type} [Fintype ι][Fintype J] (S:Table L)

-- avoid PMA of offdiagonal values
/-- Raw here through `L.Ref` rather than S.Field so may also compare a label sublimit. -/
def sample (x:ι→ E4)(v:ι→ L.Token) := S.read (points (x ∘ (Fintype.equivFin ι).symm)) (v ∘ (Fintype.equivFin ι).symm)
lemma read_from {m n:ℕ}(x:ι→ E4)(v:ι→ L.Token)(hx:Injective x)(H:S.Symmetric) (e:Fin m≃ι)(f:Fin n≃ι) :
    S.read (points (x ∘ e)) (v ∘ e)= S.read (points (x ∘ f)) (v ∘ f):= by
   classical
   have h:m=n:= by simpa using Fintype.card_congr (e.trans f.symm); -- avoid omega with coercions
   subst n; let s:=e.trans f.symm
   have hs:f ∘ s=e:= funext fun i=> f.apply_symm_apply (e i)
   have hvx: Points.rearrange s (points (x ∘ f))=points (x ∘ e):= by ext1 i; exact congrArg x (congrFun hs i)
   rw [← hvx]; have he: v ∘ e=(v ∘ f) ∘ s:= by rw [comp_assoc,hs]
   rw [he]; exact H.same s (hx.comp f.injective) _
lemma sample_from {n:ℕ}(x:ι→ E4)(v:ι→ L.Token)(hx:Injective x)(H:S.Symmetric)(e:Fin n≃ι) : S.read (points (x ∘ e)) (v ∘ e)=sample S x v := read_from S _ _ hx H _ _
lemma replaces (e:J≃ι) (x:ι→ E4)(v:ι→ L.Token)(hx:Injective x)(H:S.Symmetric): sample S (x ∘ e) (v ∘ e) = sample S x v:= sample_from S x v hx H ((Fintype.equivFin J).symm.trans e)
lemma sample_fin {n:ℕ}(x:Fin n→ E4)(v:Fin n→ L.Token)(hx:Injective x)(H:S.Symmetric): sample S x v= S.read (points x) v:= (sample_from S x v hx H (Equiv.refl _)).symm
lemma sample_points {n:ℕ}(x:Points n)(v:Fin n→ L.Token)(hx: x∈ conf n)(H:S.Symmetric): sample S x.ofLp v= S.read x v:=sample_fin S _ _ hx H
lemma shifts (x:ι→ E4)(v:ι→ L.Token)(hx:Injective x)(H:S.Homogeneous)(s:E4) : sample S ((fun i=> x i+s)) v= sample S x v:= H _ (points (x ∘ (Fintype.equivFin _).symm)) (hx.comp (Fintype.equivFin ι).symm.injective) s _

def clear (ι:Type*) (x:ι→ E4): Prop:= ∀ i:Axis,Injective fun j=> x j i
lemma clear_points (x:Points (Fintype.card ι)): clear _ x.ofLp ↔ x∈ generic _:= Iff.rfl -- general n
lemma clear_inj (x:ι→ E4)(h:clear _ x): Injective x:= fun _ _ he=> h timeAxis (congrArg (fun x:E4=> x timeAxis) he)
lemma clear_maps {x:ι→ E4}(hx:clear _ x){f:J→ι}(hf:Injective f): clear _ (x ∘ f):= fun i=> (hx i).comp hf

variable {S} (T:Table L)
/-- Physical Separated. The `T`-resolved hierarchy uses the same quotient of S. -/
def corr (x:ι→ E4)(v:ι→ S.Tag) := sample T x (expose ∘ v)
lemma at_corr (H:T.Symmetric)(ht:T.respects S)(x:ι→ E4)(v:ι→ L.Token)(hx:Injective x) : corr T x (classTokens S ∘ v) = sample T x v := at_project S T H ht (x:=points (x ∘ (Fintype.equivFin ι).symm)) (hx.comp (Fintype.equivFin ι).symm.injective) (v ∘ _)
lemma read_corr {n:ℕ}(x:ι→ E4)(v:ι→ S.Tag)(hx:Injective x)(H:T.Symmetric)(e:Fin n≃ι) : S.useAt T (points (x ∘ e)) (v ∘ e)=corr T x v:= sample_from T _ (expose∘v) hx H e
lemma corr_fin {n:ℕ}(x:Fin n→ E4)(v:Fin n→ S.Tag)(hx:Injective x)(H:T.Symmetric): corr T x v = S.useAt T (points x) v:= (read_corr T x v hx H (Equiv.refl _)).symm
lemma indices (e:J≃ι) (x:ι→ E4)(v:ι→ S.Tag)(hx:Injective x)(H:T.Symmetric): corr T (x ∘ e) (v ∘ e) = corr T x v:=replaces T e x (expose ∘ v) hx H
lemma across (x:ι→ E4)(v:ι→ S.Tag)(hx:Injective x)(H:T.Homogeneous)(s:E4) : corr T (fun i=> x i+s) v= corr T x v:= shifts T x _ hx H s
end YM.Contacts.Sensor
