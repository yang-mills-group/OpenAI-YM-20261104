import YM.MSbar.Chord.Dance
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset
variable {G:Gauge}{n:Side}
local notation "S₀"=> Site n
local notation "E"=> Edge (Site n)
local notation "N"=> n.val
private lemma backwards (o x:S₀)(i:Axis)(he:10*separation x o < N): coord o x i= -coord x o i:=by
   have hh : lift (o-x)=-(lift (x-o)):=by
       apply lift_eq_iff.mpr; refine ⟨?_,fun i=>?_⟩; rw [map_neg, wrap_lift,neg_sub]
       have h := component_le (x-o) i; unfold separation at he; change -(↑N:ℤ)< 2* -(lift (x-o) i) ∧ _; change _∧ 2* -(lift (x-o) i) ≤ (↑N:ℤ); omega
   unfold coord; rw [hh];simp
lemma foot (s:Signed)(b:S₀)(e:E):(sendEdge s b e).2=s.perm e.2:=by unfold sendEdge Step.used; split<;> simp [Step.rotate,posDir]
lemma pulse (s:Signed)(b:S₀)(e v:E)(i:Axis) (hx:100*(separation v.1 e.1+1)<N) : middle (sendEdge s b e) (sendEdge s b v) (s.perm i)=sign s i * middle e v i:=by
    let u:=e.1; let x:=v.1; let y:=s.perm i; let m:=sendEdge s b e; let d:=v.2; let j:=e.2; let A:=affine s b e.1; let D:=affine s b v.1
    have hn : 4 ≤ N:=by omega
    have he' : separation m.1 A ≤1:= by
       unfold m A sendEdge Step.used; by_cases he:s.flip e.2
       · simp only [Lattice.Step.rotate,Lattice.posDir,he]; let k:=s.perm e.2; change separation (A-step k) A ≤1; have hi:= Work.E01.sep_step_le (A-step k) k; rw [show (A-step k:S₀)+step k=A from sub_add_cancel ..] at hi; exact hi
       have hf:sendEdge s b e=(A,s.perm e.2):=by simp [A,sendEdge,posDir,Step.rotate,Step.used,he]
       exact (by change separation m.1 A ≤ _; unfold m; rw [hf]; exact separation_self A ▸ Nat.zero_le _)
    have hi: 10* separation D m.1 < N:=by
       have ht:= Nat.le_trans (separation_triangle D A m.1) (Nat.add_le_add_left (show separation A m.1 ≤ _ from separation_comm .. ▸ he') (separation D A)); rw [show separation D A= _ from spin_separation s b _ _] at ht; omega
    have he(k : Axis):sign s k *halfE k i = sign s i *halfE k i:= by unfold halfE; by_cases he:i=k <;> simp [he]
    have hg:= rises s b v.1 v.2 m.1 i hi hn
    have hy:10*separation A D<N:=by rw [show separation A D=separation e.1 v.1 from spin_separation ..,separation_comm];omega
    have hh:= rises s b e.1 e.2 D i hy hn
    have hc:= spin_coord s b v.1 e.1 i (by omega)
    unfold middle zone; rw [foot,foot]; change coord m.1 (sendEdge s b v).1 y- _+_ = _; skip; -- check
    have h : coord m.1 D y= - coord D m.1 y:=backwards _ _ _ hi
    have h' : coord A D y= - coord D A y:=backwards _ _ _ (by rw [separation_comm];exact hy); rw [he v.2] at hg; rw [he e.2] at hh
    rw [mul_add, mul_sub]; linarith only [hg,hh,h,h',hc]
end YM.MSbar.Midpoint
