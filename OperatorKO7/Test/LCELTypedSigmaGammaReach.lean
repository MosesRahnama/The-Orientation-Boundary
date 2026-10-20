import OperatorKO7.Meta.LCELDpInstance

namespace LCELTypedSigmaGammaReach

open OperatorKO7
open OperatorKO7.LCELSchema
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELTypedSigmaGamma

example : True := by
  have := godel1931LCELExternalLicenseObject
  trivial

example : True := by
  have := benchmarkTransportLCELExternalLicenseObject
  trivial

example : True := by
  have := dpEmitterLCELExternalLicenseObject
  trivial

example : True := by
  have := godel1931LCELReimportClassObject
  trivial

example : True := by
  have := benchmarkTransportLCELReimportClassObject
  trivial

example : True := by
  have := dpEmitterLCELReimportClassObject
  trivial

example : godel1931LCELInstance.externalLicenseObject.realized := by
  exact FormalLCELInstance.externalLicenseObject_realized godel1931LCELInstance

example : benchmarkTransportLCELInstance.externalLicenseObject.realized := by
  exact FormalLCELInstance.externalLicenseObject_realized benchmarkTransportLCELInstance

example : dpEmitterLCELInstance.externalLicenseObject.realized := by
  exact FormalLCELInstance.externalLicenseObject_realized dpEmitterLCELInstance

example : godel1931LCELInstance.reimportClassObject.realized := by
  exact FormalLCELInstance.reimportClassObject_realized godel1931LCELInstance

example : benchmarkTransportLCELInstance.reimportClassObject.realized := by
  exact FormalLCELInstance.reimportClassObject_realized benchmarkTransportLCELInstance

example : dpEmitterLCELInstance.reimportClassObject.realized := by
  exact FormalLCELInstance.reimportClassObject_realized dpEmitterLCELInstance

example :
    godel1931LCELInstance.externalLicenseObject.realized
      ↔ godel1931LCELInstance.externalLicenseWitness := by
  exact godel1931LCELInstance.externalLicenseMatchesWitness

example :
    benchmarkTransportLCELInstance.externalLicenseObject.realized
      ↔ benchmarkTransportLCELInstance.externalLicenseWitness := by
  exact benchmarkTransportLCELInstance.externalLicenseMatchesWitness

example :
    dpEmitterLCELInstance.externalLicenseObject.realized
      ↔ dpEmitterLCELInstance.externalLicenseWitness := by
  exact dpEmitterLCELInstance.externalLicenseMatchesWitness

example :
    godel1931LCELInstance.reimportClassObject.realized
      ↔ godel1931LCELInstance.reimportClassWitness := by
  exact godel1931LCELInstance.reimportClassMatchesWitness

example :
    benchmarkTransportLCELInstance.reimportClassObject.realized
      ↔ benchmarkTransportLCELInstance.reimportClassWitness := by
  exact benchmarkTransportLCELInstance.reimportClassMatchesWitness

example :
    dpEmitterLCELInstance.reimportClassObject.realized
      ↔ dpEmitterLCELInstance.reimportClassWitness := by
  exact dpEmitterLCELInstance.reimportClassMatchesWitness

example : True := by
  have := godel1931LCELInstance.externalLicenseObject.designated_sentence_eq_blocked
  have := godel1931LCELInstance.externalLicenseObject.designated_reflects
  have := godel1931LCELInstance.externalLicenseObject.designated_licensedAdmission
  trivial

example : True := by
  have := benchmarkTransportLCELInstance.reimportClassObject.designated_sentence_eq_imported
  have := benchmarkTransportLCELInstance.reimportClassObject.designated_certifies
  have := benchmarkTransportLCELInstance.reimportClassObject.designated_true
  trivial

example : True := by
  have := dpEmitterLCELInstance.externalLicenseObject.designated_not_provable
  have := dpEmitterLCELInstance.externalLicenseObject.designated_true
  have := dpEmitterLCELInstance.reimportClassObject.designated_sentence_eq_imported
  trivial

example : True := by
  have :=
    godel1931LCELInstance.externalLicenseObject.designated_sentence_eq_blocked
  have :=
    benchmarkTransportLCELInstance.externalLicenseObject.designated_sentence_eq_blocked
  have :=
    dpEmitterLCELInstance.externalLicenseObject.designated_sentence_eq_blocked
  trivial

example : True := by
  have :=
    godel1931LCELInstance.reimportClassObject.designated_sentence_eq_imported
  have :=
    benchmarkTransportLCELInstance.reimportClassObject.designated_sentence_eq_imported
  have :=
    dpEmitterLCELInstance.reimportClassObject.designated_sentence_eq_imported
  trivial

end LCELTypedSigmaGammaReach
