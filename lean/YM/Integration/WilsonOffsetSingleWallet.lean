import YM.Integration.WilsonPhysicalHistoryWalletPhysicalCofactor

/-! Buy the genuine occupied singleton, at both of its true sites,
in the signed original history wallets, retaining every hard partner. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetSingleWallet
open Function Set Finset MeasureTheory Lattice Wilson RG Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato OPE OPE.Therm WilsonCoeffUV RGComparison.Core16.Spool
open WilsonConditionalTaylorLabels WilsonReportForwardTransfer WilsonOffsetJointRoster WilsonOffsetPhysicalPair
open WilsonPhysicalHistoryWalletExperiment WilsonPhysicalHistoryWalletSignedPair
open scoped Classical BigOperators
variable {G:Gauge} {d:ℕ}
abbrev Row (G:Gauge) (d:ℕ):=((frames G).level d).Index
def roster (i:Row G d):Roster G:=[⟨d,i⟩]
def slot (i:Row G d):Fin (roster i).length:=⟨0,by simp [roster]⟩
def word {n:Side} (i:Row G d) (z e:Site n) (U:Config G n):ℂ:=WilsonOffsetPhysicalPair.basis i z U-WilsonOffsetPhysicalPair.basis i e U

theorem letter {n:Side} (i:Row G d) (z:Site n):Continuous (WilsonOffsetPhysicalPair.basis i z):=
  (localSection G d).continuous_places _ _

def opening (R:Run G) (d:ℕ):ℕ:=Finset.univ.sup (fun i:Row G d=>opens R (roster i))
def registered (R:Run G) {N p k u:ℕ} (h:k≤u) (i:Row G d) (z e:Site (R.family.side (u+1) p))
    (part:Bool) (Qz Qe:Coefficient ((frames G).level 0) (R.family.side k p)):Prop:=
  let a:=roster i
  let v:=slot i
  let s:Finset (Fin a.length):={v}
  let o:Fin a.length→Site _:=fun _=>e
  WilsonPhysicalHistoryWalletDeposit.Registered R (N:=N) h a s o v z z part Qz ∧
  WilsonPhysicalHistoryWalletDeposit.Registered R (N:=N) h a s o v e e part Qe

theorem original (R:Run G) (simple:G.Simple) {N p k u:ℕ} (top:u<N) (h:k≤u)
    (i:Row G d) (z e:Site (R.family.side (u+1) p)) (late:opening R d≤k):
    ∃Qz Qe:Bool → Coefficient ((frames G).level 0) (R.family.side k p),
      (∀part,registered R (N:=N) h i z e part (Qz part) (Qe part)) ∧
      ∀V,exterior (C:=R.family) (N:=N) (h.trans u.le_succ) (word i z e) V=
        WilsonPhysicalHistoryWalletPhysicalCofactor.cash R (N:=N) h z e (Qz false) (Qe false) V +
        Complex.I*WilsonPhysicalHistoryWalletPhysicalCofactor.cash R (N:=N) h z e (Qz true) (Qe true) V:=by
  let a:=roster i
  let v:=slot i
  let s:Finset (Fin a.length):={v}
  let o:Fin a.length→Site _:=fun _=>e
  have lower:opens R a≤k:=(Finset.le_sup (f:=fun j:Row G d=>opens R (roster j)) (Finset.mem_univ i)).trans late
  have inside:v∈s:=Finset.mem_singleton_self _
  choose Qz Qe zfund efund _ ht using fun part=>WilsonPhysicalHistoryWalletSignedPair.original R simple top h a s o v inside z e z e part lower
  refine ⟨Qz,Qe,fun part=>⟨zfund part,efund part⟩,?_⟩
  let plane:=fun part (U:Config G (R.family.side (u+1) p))=>(↑(look part (word i z e U)):ℂ)
  have placed (U:Config G (R.family.side (u+1) p)):
      field a (s.erase v) o U*(one a v z U-one a v e U)=word i z e U:=by
    rw [finite]
    simp only [s,Finset.erase_singleton,Finset.prod_empty,one_mul]
    rfl
  have read (part:Bool):exterior (C:=R.family) (N:=N) (h.trans u.le_succ) (plane part)=
    response R (N:=N) h a s o v z e part:=by
    unfold response
    apply congrArg (fun f=>exterior (C:=R.family) (N:=N) (h.trans u.le_succ) f)
    funext U;rw [placed]
  have separate:word i z e=fun U=>plane false U+Complex.I*plane true U:=by
    funext U
    change word i z e U=(↑((word i z e U).re):ℂ)+Complex.I*(↑((word i z e U).im):ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im _).symm
  letI:IsProbabilityMeasure (scene R.family.path N p (u+1)):=probability R.makes.wilson top
  have cw:Continuous (word i z e):=(letter i z).sub (letter i e)
  have hp (part:Bool):Integrable (plane part) (scene R.family.path N p (u+1)):=
    (Complex.continuous_ofReal.comp ((look part).continuous.comp cw)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  intro V
  rw [separate,WilsonPhysicalHistoryWalletSum.added R (h.trans u.le_succ) top _ _ (hp false) ((hp true).const_mul _),
    WilsonPhysicalHistoryWalletSum.scaled R (h.trans u.le_succ) top Complex.I (plane true),read false,read true]
  change response R (N:=N) h a s o v z e false V+Complex.I*response R (N:=N) h a s o v z e true V=_
  exact congrArg₂ (fun x y:ℂ=>x+Complex.I*y) (ht false V) (ht true V)

end YM.Integration.WilsonOffsetSingleWallet
