import YM.Integration.QLocalMarkedJoinedLinear

/-! A genuine compulsory insertion in the existing nonquiet marked gas,
on the original compatible Wilson supports and at all configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedRelease
open Function Finset Lattice RG Wilson Marker Overlay Extra.Trajectories Extra.Histories Planned.GuardedAtom
open Push.AbsoluteSums QLocalMarkedJoinedCofactor QLocalMarkedJoinedSeries
open QLocalMarkedJoinedLinear QLocalCompulsoryJoinedTape
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

theorem absolute {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {ι:Type*} {a:ι→Poly Γ} (w:V→ℝ) (h:Summable a) :
    Summable (fun i=>Poly.price w (a i)) :=
  summable_sum (s:=Finset.univ) (fun s _=>((Poly.get s).summable h).norm.mul_left (Poly.toll w s))

theorem double (a:Bands Γ W) (f:ℕ→Poly Γ) (U:Config G n)
    (pay:Summable f) (old:Summable (fun b=>a.packet b U)) :
    Summable (input (W:=W) (fun i=>a.each i U) f U) := by
  let w:V→ℝ:=fun _=>1
  have pos:∀i,0<w i:=fun _=>zero_lt_one
  let p r:=Poly.price w (f r)
  let q b:=Poly.price w (a.packet b U)
  have hp:SumBudget p (∑' r,p r):=⟨fun r=>Poly.nonnegative pos _,absolute w pay,le_rfl⟩
  have hq:SumBudget q (∑' b,q b):=⟨fun b=>Poly.nonnegative pos _,absolute w old,le_rfl⟩
  exact (Poly.budgeted pos (budget_prod hp hq).2.1 (fun i=>Poly.multiplication pos ..)).1

theorem issued (K:Guard.Keeper W.p W.activities) (a:Bands Γ W) (s:Γ.Mode) (hs:s≠Γ.quiet)
    (f:ℕ→ Config G n→ℂ) (U:Config G n) (hot:∀r,f r U≠0→¬Healthy W.p.threshold (Y r) U)
    (pay:Summable (fun r=>f r U)) (entries:∀i,Summable (fun j=>a.tagged i j U))
    (old:Summable (fun b=>a.packet b U)) :
    let d:=addition (Y:=Y) K a s f
    let b:=bands a d
    Summable (fun I=>b.packet I U) ∧
    b.cluster U=Poly.pass (Poly.send s (∑' r,f r U))*a.cluster U := by
  let d:=addition (Y:=Y) K a s f
  let b:=bands a d
  let z r:=Poly.send s (f r U)
  have grouped : HasSum z (Poly.send s (∑' r,f r U)) := pay.hasSum.map (Multi.sendC s) (Bands.sends s)
  have hz : Summable z := grouped.summable
  have crossed:=QLocalMarkedJoinedSeries.relative K a z U
    (fun r hn=>hot r (fun zero=>hn (by simp [z,zero]))) hz (double a z U hz old) old
  let pair:=output (Y:=Y) K (fun i=>a.each i U) z U
  let rpair (p:Finset ℕ×ℕ):=pair (p.2,p.1)
  have hr:Summable rpair:=crossed.1.prod_symm
  have rs:Summable (fun I=>∑' i,rpair (I,i)):=hr.prod
  have value (I:Finset ℕ):b.packet I U=a.packet I U+(∑'i,rpair (I,i)):=by
    rw [QLocalMarkedJoinedLinear.packet (a:=a) (b:=b) d U I
        (fun i=>QLocalCompulsoryJoinedTape.each a d i U (silence K a s hs f i U) (entries i))
        (fun i j=>square_rows K a s hs f i j U)]
    rw [tsum_eq_sum (s:=I) (fun i hi=>by simp [rpair,pair,output,QLocalMarkedJoinedCofactor.coat,hi])]
    rfl
  have chosen:Summable (fun I=>b.packet I U):=(old.add rs).congr (fun I=>(value I).symm)
  refine ⟨chosen,?_⟩
  have sum:(∑' I,∑'i,rpair (I,i))=(∑' r,z r)*a.cluster U:=hr.tsum_prod.symm.trans
    (((Equiv.prodComm (Finset ℕ) ℕ).tsum_eq pair).trans crossed.2)
  have nz:s.val.Nonempty:=Finset.nonempty_iff_ne_empty.mpr (fun h=>hs (Subtype.ext h))
  change (∑' I,b.packet I U)=_
  rw [tsum_congr value,old.tsum_add rs,sum,grouped.tsum_eq,pass_send nz,add_mul,one_mul]
  rfl

end YM.Integration.QLocalMarkedJoinedRelease
