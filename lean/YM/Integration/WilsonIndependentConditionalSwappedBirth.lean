import YM.Integration.WilsonIndependentConditionalCoverBirth

/-! The same signed cover attachment with its marked and unmarked factors
interchanged. A real simultaneous two-end sum justifies the exchange. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalSwappedBirth
open Function RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Budget.Tuple RegulatorIR.Diagram
open Lattice Laurent Bloch Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open WilsonIndependentConditionalCoverKnot
open scoped Classical BigOperators
variable {X α:Type}{i j r:ℕ}

theorem commuted (K:Layer X X)(T:Packet X (i+1))(U:Packet X (j+1))(x:Tuple X (i+j))
    (h:Summable (entry K T U x)):
    knot (Function.swap K) U T (x∘finAddFlip.symm)=knot K T U x:=by
  let e:=Equiv.prodComm X X
  have left:cutLeft (r:=j) (s:=i) (x∘finAddFlip.symm)=cutRight x:=by
    funext z;change x (finAddFlip.symm (Fin.castAdd i z))=x (Fin.natAdd i z)
    rw [←finAddFlip_apply_natAdd z i,Equiv.symm_apply_apply]
  have right:cutRight (r:=j) (s:=i) (x∘finAddFlip.symm)=cutLeft x:=by
    funext z;change x (finAddFlip.symm (Fin.natAdd j z))=x (Fin.castAdd j z)
    rw [←finAddFlip_apply_castAdd z j,Equiv.symm_apply_apply]
  have eqn (q:X×X):entry (Function.swap K) U T (x∘finAddFlip.symm) (e q)=entry K T U x q:=by
    unfold entry;rw [left,right];dsimp [Function.swap,e];ring
  have other:Summable (entry (Function.swap K) U T (x∘finAddFlip.symm)):=e.summable_iff.mp (h.congr (fun q=>(eqn q).symm))
  rw [←sum _ _ _ _ other,←sum _ _ _ _ h,←e.tsum_eq]
  exact tsum_congr eqn

private theorem permuted {n m:ℕ}(f:Fin n≃Fin m)(T:Packet X n)(U:Packet X m)
    (h:∀ x,U (x∘f.symm)=T x)(x:Tuple X n):
    Packet.symmetry U (x∘f.symm)=Packet.symmetry T x:=by
  rw [symmetry_at,symmetry_at,Fintype.card_congr (Equiv.permCongr f)]
  congr 1
  rw [←Equiv.sum_comp (Equiv.permCongr f)]
  apply Finset.sum_congr rfl;intro v _
  rw [←h (x∘v)]
  apply congrArg U;funext z;simp

private theorem bound [Fintype α] (K:ropes Cover α α)(T U:Gen ℝ (Cloth α))
    {A:(n:Side)→ ropes (Site n) α α}{V Y:(n:Side)→Gen ℝ (Co n α)} {p:Cover}
    (h:Pilots A K)(hi:Yields (fun n=>V n (i+1)) (T (i+1)))
    (hj:Bends p (fun n=>Y n (j+1)) (U (j+1)))(x:dock Cover α (i+j)):
    Summable (entry K (T (i+1)) (U (j+1)) x):=by
  let e:=finTwoArrowEquiv (Cloth α)
  let t:= entry K (T (i+1)) (U (j+1)) x
  have wage:=WilsonIndependentConditionalCoverFare.original (branch_read h hi hj (rfl:i+j=i+j)) x
  have eqn (q): rill K T U (i+j) i j x q=weight i j*t (e q):=by
    rw [rill_spell];unfold weight t entry
    change _=_*(T (i+1) (Fin.cons (q 0) (x∘Fin.castAdd j))*(K (q 0) (q 1)*U (j+1) (Fin.cons (q 1) (x∘Fin.natAdd i))))
    rw [smul_eq_mul];ring
  have hv:Summable (fun q=>weight i j*t q):=e.summable_iff.mp (wage.congr eqn)
  have pos:0<weight i j:=by unfold weight;positivity
  simpa only [←mul_assoc,inv_mul_cancel₀ pos.ne',one_mul] using hv.mul_left (weight i j)⁻¹

private theorem transport {n m:ℕ}(e:n=m)(T:Packet X n)(x:Tuple X m):
    (e ▸ T : Packet X m) x=T (x∘finCongr e):=by subst m;rfl

theorem aligned [Fintype α] {K:ropes Cover α α}{A:(n:Side)→ ropes (Site n) α α}{p:Cover}
    {T U:Gen ℝ (Cloth α)}{V Y:(n:Side)→ Gen ℝ (Co n α)} (hc:Pilots A K)
    (hi:Yields (fun n=>V n (i+1)) (T (i+1)))(hj:Bends p (fun n=>Y n (j+1)) (U (j+1)))(eqn:i+j=r):
    matchTwo K T U r (i,j)=matchTwo K.transpose U T r (j,i):=by
  subst r
  let e:Fin (i+j)≃Fin (j+i):=finAddFlip
  let f:Fin (j+i)≃Fin (i+j):=finCongr (Nat.add_comm j i)
  let W:=knot K.transpose (U (j+1)) (T (i+1))
  let P:=knot K (T (i+1)) (U (j+1))
  have equal (x:Tuple (Cloth α) (i+j)):W (x∘e.symm)=P x:=
    commuted K _ _ x (bound K T U hc hi hj x)
  have reads (x:Tuple (Cloth α) (i+j)): Packet.symmetry W (x∘f)=Packet.symmetry P x:=by
    let π:=f.trans e
    have ix:(x∘e.symm)∘π=x∘f:=by funext t;simp [π]
    rw [←ix,is_symmetry W,permuted e P W equal]
  funext x
  have g:j+i=i+j:=Nat.add_comm j i
  unfold matchTwo
  rw [dif_pos (rfl:i+j=i+j),dif_pos g,transport g]
  simp only [Pi.smul_apply,smul_eq_mul]
  change _=(((j:ℝ)+1)*((i:ℝ)+1))*Packet.symmetry W (x∘f)
  rw [reads,mul_comm ((j:ℝ)+1)]

end YM.Integration.WilsonIndependentConditionalSwappedBirth
