import YM.WilsonCoeffUV.Wick.Voltage
/-!
# Formal W matrices through all W tales. Shift lower-bound unity at horizon records. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm Fountain
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f n:Side}{U V α:Type*} {G:Gauge} {h D i j k e n' m N r:ℕ}{F:Labels.Frame G h} {H:Hol G}
variable {z ξ σ A' B:ℝ} {s t:ℝ}
variable {A:Levels G}{Ñ:ChartRatio G}{I:Cloister G h}{J:Usage A Ñ m}

lemma bureau (F:Frame G h)(P:Island F D)(p:Shimmer P)(H:Hol G)(w:h<D)(hp:m<N)(g:G.Simple)(ht:LocalRatio Ñ)(v:relight A Ñ m J I)(j:Alma F)(Y:ChamberTen G (Vote D) (valence F j))(q:Hedged Y):
    let T:=lineS (prismata F (descend A Ñ N m P).2) 0
    echoS F (hall (loose A m) h (shuttleM (feedA A N m)) Y) j = ∑ i, identum T j i * echoS F Y i:=by
    obtain ⟨Q,hQ⟩:= pickS (J.postStand hp g ht) v.1.symm
    obtain ⟨R⟩:= v.2 N hp g ht Q hQ
    have he :hall (loose A m) h (shuttleM (feedA A N m)) Y= hall (inkPin I).patch h Q.Q Y ∧ dragCup Bank.terrain J.s J.D Q.Q:=by
       have hu (X:Gear G)(U:Stand X)(t:J.gear=X)(u:HEq U (J.postStand hp g ht)) : hall (loose A m) h (shuttleM (feedA A N m)) Y=hall X.patch h U.Q Y ∧ dragCup Bank.terrain J.s J.D U.Q:=by
          subst X; rw [eq_of_heq u]; exact ⟨rfl,(J.cardG.shift N N N hp le_rfl le_rfl).1.oneP⟩
       exact hu _ _ v.1.symm hQ
    intro T
    unfold T; rw [show (descend A Ñ N m P).2=legion Q P.2 from byPath A Ñ hp g ht P J I v.1 Q hQ, he.1]
    exact scoop_F P p Q R w he.2 (J.width.trans J.win) H j Y q

def wickT (A:Levels G)(m N k:ℕ)(F:Frame G h)(Y:Single G D) : Alma F → ℝ:=fun i=>echoS F (paveS A m N k (Y 0) (valence F i)) i
def wickM (A:Levels G)(m N:ℕ)(F:Frame G h)(P:Thesis F D): Wall F:= of fun i j=> wickT A m N h F (P j) i
lemma towardsM (X:Single G D)(P:Estate G D)(K:Island F D)(q:Shimmer K)(p:Solo k P X)(hq:k≤h)(H: Hol G)(w:h<D)(hp:m<N)(g:G.Simple)(ht:LocalRatio Ñ)(v:relight A Ñ m J I):
    wickT A m N h F (marchT A Ñ N m h X)= identum (lineS (prismata F (descend A Ñ N m K).2) 0)*ᵥ wickT A (m+1) N h F X:=by
    set S:= lineS (prismata F (descend A Ñ N m K).2) 0
    funext i; unfold Matrix.mulVec dotProduct
    let Q:=paveS A (m+1) N h (X 0)
    have hx : Stakes X:= ⟨solo_pure p,solo_upright p,fun j r=>solo_mural p r j⟩
    have h' : ∀ j r,Standby (X j r):=solo_stretch p
    rw [wickT,descent A Ñ X hp g ht (shell_mon (solo_shape p) hq) hx h', show echoS F (hall _ h _ _) i=∑ j,identum S i j * echoS F (Q (valence F i)) j from bureau F K q H w hp g ht v i _ (winds_carve A X P p h hq N (m+1) (valence F i))]
    apply Finset.sum_congr rfl; intro j _
    by_cases u:valence F i= valence F j
    · apply congr_arg (identum S i j*·); rw [u]; rfl
    simp only [identum,Matrix.of_apply, if_neg u,zero_mul]
lemma iceFleet {P: U→Estate G D}{X:U → Single G D} {c:U→ℝ} (S:Finset U)(p:∀ i∈S,∀ j,Bends 0 (fun n=> P i n 0 j) (X i 0 j)): paveS A m N k (∑ i∈S,c i • X i 0)=∑ i∈S,c i • paveS A m N k (X i 0):=by
    ext1 r; let V (n:Side):= ∑ i∈S,c i • P i n 0
    have he j:Bends 0 (fun n=>V n j) ((∑ i∈S,c i • X i 0) j):= leaderT (P:=fun n i=>c i • P i n 0) (F:=fun i=>c i • X i 0) (fun i pi=> (p i pi j).μ (c i))
    apply (mason_path (recruit A ..) (Q:=V) k he r).exten
    exact (leaderT (P:=fun n i=> c i • carve k (blues A N m n) (P i n 0)) (F:=fun i=>c i • paveS A m N k (X i 0)) (fun i hi=>(mason_path (recruit A ..) (Q:=fun n=>P i n 0) k (p i hi) r).μ _)).congr (Eventually.of_forall (fun n=>by unfold V; simp_rw [carveMe, map_sum, map_smul]))
lemma lumber (P:Island F D)(v: Coil F)(p:Shimmer P)(m N:ℕ): wickM A m N F (impose P.2 v)=wickM A m N F P.2*lineS v 0:=by
    ext x y; unfold wickM wickT; rw [Matrix.of_apply, show impose P.2 v y 0=∑ i,lineS v 0 i y • P.2 i 0 from by simp_rw [impose,Finset.sum_apply,affix,Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; rfl, iceFleet (A:=A) (P:=fun i n=>P.1 n i) Finset.univ (fun i _ j=> (p.scan.solo i).shore 0 j),Finset.sum_apply,echo_sum, Matrix.mul_apply]
    · exact Finset.sum_congr rfl (fun i _=> (echo_mu F x _ _).trans (mul_comm ..))
    exact fun i _=> ((winds_carve A (P.2 i) _ (p.scan.solo i) h (valence_cap ..) N m _).tax).μ _
section
variable {T:SectionData F}{p:h<D}{E W:Credit}(L:Theatre H T p e E W)
theorem intercore (a:L.V.anchor≤m)(t:m<N): let P:=L.lore N m; let Q:=L.lore N (m+1); let J:=Jacob L.V.draws L.V.paid T p N m; wickM L.V.draws m N F P.2 * lineS J 0= identum (lineS J 0)* wickM L.V.draws (m+1) N F Q.2:=by
    intro P Q J
    have hP:Shimmer P:= (production L t.le a).1; have hQ:Shimmer Q:= (production L (show m+1≤N from t) (by omega)).1; let K:= descend L.V.draws L.V.paid N m Q
    rw [← lumber P J hP m N, show impose P.2 J=K.2 from ?_]
    · ext i j; exact congr_fun (towardsM (Q.2 j) (fun n=>Q.1 n j) Q hQ (hQ.scan.solo _) (valence_cap ..) H p t L.V.hG L.V.green (L.effort _ a)) i
    have hp:P=reglazed K:= marched _ _ _ _ t
    rw [hp]; exact refluent (V:=K) (stellarized (leaseN L a t))
end
end YM.WilsonCoeffUV.Cosmos
