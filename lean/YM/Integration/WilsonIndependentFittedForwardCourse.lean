import YM.Integration.WilsonIndependentFittedForwardStep

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedForwardCourse
open WilsonCoeffUV WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open WilsonIndependentFittedForwardStep
open scoped BigOperators Classical
variable {G:Gauge}{h D e:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}{E W U:Credit}
abbrev Course:=CourseS H T p e E W U
def side (t:Course (H:=H) (T:=T) (p:=p) (e:=e) (E:=E) (W:=W) (U:=U))(i:ℕ):Side:=
  (loose t.vols.draws (t.spur+i)).L
def normalized (t:CourseS H T p e E W U)(N:ℕ)(b:Bool)(i:ℕ):Coil F:=
  coupon (side t i) h • aftGear t.vols.draws t.vols.paid T p N t.spur t.length b i
def reversed (t:CourseS H T p e E W U)(N:ℕ)(b:Bool)(i:ℕ):Coil F:=
  normalized t N b (t.length-1-i)

theorem earned (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W U:Credit)(b:Bool)(i:ℕ)(hi:i≤e):
    let d:=CourseS.length (H:=H) (T:=T) (p:=p) (e:=e) (E:=E) (W:=W) (U':=U)
    let P (t:CourseS H T p e E W U):=reversed t t.I.n b
    let Q (t:CourseS H T p e E W U):=reversed t t.I.N b
    CreditsS (rubP d CourseS.Age) (rubP d CourseS.cab)
      (fun a=>lineS (stairs d P a) i) (fun a=>lineS (stairs d Q a) i):=by
  intro d P Q
  let x:=Bank.rub d CourseS.Age
  let θ:=Bank.rub d CourseS.cab
  have HC:=CourseB H T p e E W U
  have hb:Brite x θ:=⟨fun z=>HC.large _,fun z=>HC.dist _⟩
  let rev (a:Jag d):Jag d:=⟨a.cargo,a.cargo.length-1-a.coin,by
    change a.cargo.length-1-a.coin<a.cargo.length
    have paid:a.coin<a.cargo.length:=a.credit
    omega⟩
  let M (a:Jag d)(N):=Jacob a.cargo.vols.draws a.cargo.vols.paid T p N (a.cargo.spur+a.coin)
  let Γ (a:Jag d)(N):=warp a.cargo.vols.draws a.cargo.vols.paid N a.cargo.spur a.cargo.length b a.coin
  have credit (a:Jag d)(N:ℕ)(hn:a.cargo.I.b≤N):leaseM (side a.cargo a.coin) F (lineS (M a N) 0):=by
    apply leaseN a.cargo.robe.arch
    · exact a.cargo.root.trans (by omega)
    have hg:a.coin<a.cargo.length:=a.credit
    have hf:a.cargo.spur+a.cargo.length≤a.cargo.I.b:=a.cargo.far
    omega
  have earn (l:ℕ)(hl:l ≤ i):CreditsS x θ
      (fun a=>lineS (Chars F (Γ a a.cargo.I.n) (M a a.cargo.I.n)) l)
      (fun a=>lineS (Chars F (Γ a a.cargo.I.N) (M a a.cargo.I.N)) l):=
    Chars.glide hb (fun _ t=>edgeC H T p e E W U (t.trans (hl.trans hi)) b)
      (fun _ t=>windowBounds H T p e E W U (t.trans (hl.trans hi)))
  apply baron HC (fun t=>t.I.buySpan)
  · intro l hl a c
    obtain ⟨k,C,hC,fee⟩:=earn l hl a c
    refine ⟨k,C,hC,fun z=>?_⟩
    let j:=rev z
    let u:=coupon (side j.cargo j.coin) h
    change twain _ _ (lineS (u • Chars F (Γ j j.cargo.I.n) (M j j.cargo.I.n)) l a c)
      (lineS (u • Chars F (Γ j j.cargo.I.N) (M j j.cargo.I.N)) l a c)
    rw [line,line]
    exact toll_unchanged (fee j) ((Real.norm_of_nonneg (coupon_pos _ _).le).trans_le (coupon_le _ _)) (hb.dist j)
  · intro z
    let j:=rev z
    exact step (side j.cargo j.coin) (M j j.cargo.I.n) (M j j.cargo.I.N) (Γ j _) (Γ j _)
      (credit j _ j.cargo.I.hd) (credit j _ j.cargo.I.hg)

theorem normalized_price (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W U:Credit)(b:Bool)(i:ℕ)(hi:i≤e):
    ∃C:Credit,∀t:CourseS H T p e E W U,∀a c:Alma F,
      twain (C.buy t.Age) t.cab
        (lineS (hillcrest (normalized t t.I.n b) t.length) i a c)
        (lineS (hillcrest (normalized t t.I.N b) t.length) i a c):=by
  obtain ⟨C,paid⟩:=cashier ⟨fun z=>z.cargo.I.warm,fun z=>(trail_pos ..).le⟩
    (earned H T p e E W U b i hi)
  refine ⟨C,fun t a c=>?_⟩
  have hearing:=paid ⟨t,t.length,le_rfl⟩ a c
  change twain _ _ (lineS (steepen (fun j=>normalized t t.I.n b (t.length-1-j)) t.length) i a c)
    (lineS (steepen (fun j=>normalized t t.I.N b (t.length-1-j)) t.length) i a c) at hearing
  simpa only [WilsonIndependentFittedForwardStep.reverse] using hearing

end YM.Integration.WilsonIndependentFittedForwardCourse
