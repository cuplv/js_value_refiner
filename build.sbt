name := "js_value_refiner"

organization := "edu.colorado.plv"

version := "0.1.0"

scalaVersion := "2.10.4"

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.0" % "test"

// set scalatest options: -o standard output, D durations
testOptions in Test += Tests.Argument("-oD")

// JVM arguments: 8G heap size, 2M stack size
javaOptions ++= Seq("-Xmx8G", "-Xss2M")

artifactPath in packageBin in Compile := baseDirectory.value / "dist" / "js_value_refiner.jar"