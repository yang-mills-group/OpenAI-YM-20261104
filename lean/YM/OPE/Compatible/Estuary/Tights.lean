import YM.OPE.Compatible.Estuary.Happy
/-!
# Composition jet estimation on trans invariant pages. Point insertions from readers (`boom`). Keep m on every step for any r (finite post factors). Append untouched tail.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I:Type}[Fintype I]{r n m d h:ℕ}{G:Gauge} {X:Side}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
lemma insertion_one (q:Script I (n+1))(hq: Summable q)(v: Fin n→ deck I X)(u: deck I X): library X q (Fin.cons u v)= dotProduct (boom q v) u:=by
    let T:=listV q X; let L := (ContinuousMultilinearMap.apply ℝ _ ℝ v) ∘L T.curryLeft; have hh(x): L x= library X q (Fin.cons x v):= muses q hq _
    rw [← hh, show L u=L (∑ j:Tab I X,u j • (deltaH j)) from congr_arg L (by ext j; simp [deltaH,Pi.single_apply,Finset.sum_apply,mul_ite]),map_sum]; apply Finset.sum_congr rfl fun i _=> by rw [map_smul,hh]; exact mul_comm .. -- congr
abbrev pump (Q:Script I (r+1))(P:Script I (n+1)): Script I (r+n):= cotton (unitRow _) Q P
lemma pomp (Q:Script I (r+1))(hQ: Summable Q)(P: Script I (n+1))(hP:Summable P)(x: Fin n→deck I X)(v: Fin r→deck I X): library X Q (Fin.cons (boom P x) v) = library X (pump Q P) (Fin.append v x):=by
    rw [pump,dairies _ (⟨1,1,one_pos,fun x y=> Work.F08.strip_unit x y⟩) _ hQ _ hP, acts_unit, Matrix.one_mulVec, insertion_one Q hQ]
def redact (q:Script I m)(h:m=n):Script I n:= h ▸ q
omit [Fintype I] in
lemma redactTut (q: Script I m)(h:m=n)(p: Fin n→deck I X):library X (redact q h) p=library X q (p ∘ Fin.cast h):=by subst h; rfl
omit [Fintype I] in
lemma redactP (q:Script I m){b:ℝ}(h:m=n)(hp:soot r q b):soot r (redact q h) b:=by subst h; exact hp
-- Variable k but all finite. q cost Ward. p : Fin r→...
lemma apprentices (k:Fin r→ℕ)(m d:ℕ)(p:(i: Fin r)→Script I (k i+1))(h:∀ i,∃ c,soot m (p i) c): ∃ z:ℝ, ∀ (q:Script I (r+d)) c,soot m q c→ ∃ P: Script I ((∑ i,k i)+d), soot m P (z*c) ∧ ∀ (n:Side)(v:deck I n), narrate n P v= library n q (Fin.append (fun j=> boom (p j) fun _=> v) (fun _=>v)) :=by
    induction r generalizing d with
    | zero=>
       refine ⟨1,fun q c h=>?_⟩
       have hh :(∑ i,k i)=0:=by simp
       refine ⟨redact q (by rw [hh]),?_,fun n v=>?_⟩
       · rw [one_mul]; exact redactP q _ h
       unfold narrate; rw [redactTut, Fin.append_left_nil _ _ rfl]; rfl
    | succ r ih=>
       let K j:=k (Fin.succ j); let P(j):Script I (K j+1):= p (Fin.succ j); obtain ⟨a,H⟩:= ih K (d+k 0) P fun j=>h _
       obtain ⟨y,hY⟩:= h 0; let C:= y*(widthCost 1 m)*((3*k 0+2:ℕ):ℝ)^m; refine ⟨a*C,fun q c he=>?_⟩
       have heq:r+1+d=r+d+1:=by omega
       let Q:Script I (r+d+1):= redact q heq; let T:= pump Q (p 0); let L:=redact T (show r+d+k 0=r+(d+k 0) from Nat.add_assoc ..)
       have hc: soot m Q c:=redactP q _ he; have hb : soot m L (C*c):=by
           apply redactP; exact (cotton_cost (A:=unitRow _) (U:=1) (s:=1) (fun _ _=>Work.F08.strip_unit ..) one_pos zero_le_one hc hY).tips (le_of_eq (by unfold C; ring))
       obtain ⟨Z,hZ,Hz⟩:= H L _ hb; have hg : (∑ i,K i)+(d+k 0)=(∑ i,k i)+d:=by rw [Fin.sum_univ_succ]; unfold K; omega
       refine ⟨redact Z hg,?_,fun n v=>?_⟩
       · rw [mul_assoc a]; exact redactP Z _ hZ
       unfold narrate; rw [redactTut]; change narrate n Z v=_; rw [Hz n v]; rw [show L=redact T (Nat.add_assoc ..) from rfl,redactTut]
       let f(i:Fin r):= boom (P i) (fun _=>v) 
       have ht':((Fin.append f (fun _ :Fin (d+k 0)=>v)) ∘ Fin.cast (Nat.add_assoc ..))=Fin.append (Fin.append f (fun _ :Fin d=>v)) (fun _ :Fin (k 0)=>v):=by
          rw [Fin.append_assoc, show Fin.append (fun _ :Fin d=>v) (fun _ :Fin (k 0)=>v)=fun _=>v from ?_]; exact funext fun j=> Fin.addCases (m:=d) (n:=k 0) (motive:=fun i=>Fin.append _ _ i=v) (fun _=>Fin.append_left ..) (fun _=>Fin.append_right ..) j
       change library n T ((Fin.append f _)∘_)= _; rw [ht', show library n T _= _ from (pomp Q (sootS hc) (p 0) (sootS hY) (fun _=>v) _).symm];rw [show Q=redact q heq from rfl,redactTut]; apply congr_arg (library n q); let F(j:Fin (r+1)):= boom (p j) (fun _=>v); have he: F= Fin.cons (F 0) f:=by ext1 i; refine Fin.cases rfl (fun _=>rfl) i
       change Fin.cons _ _∘Fin.cast _= Fin.append F (fun _=> v); conv_rhs=>rw [he, Fin.append_cons]
end Script
end YM.OPE.Flume
