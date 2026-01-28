package interactive.groupchat

import loci._
import loci.transmitter.rescala._
import loci.serializer.upickle._
import loci.communicator.tcp._
import loci.transmitter.IdenticallyTransmittable
import upickle.default._
import rescala.default._
import upickle.default.macroRW

import java.text.SimpleDateFormat
import java.util.{Calendar, Date}
import scala.io.StdIn.readLine

case class Message(text: String, sender: String, sentTimeInMillis: Long) {
  override def toString: String = {
    val time = new SimpleDateFormat("HH:mm") format new Date(sentTimeInMillis)
    s"$time $sender: $text"
  }
}

object Message {
  implicit val authorTransmittable: IdenticallyTransmittable[Message] = IdenticallyTransmittable()
  implicit val authorSerializer: ReadWriter[Message] = macroRW[Message]
}


@multitier object GroupChat {
  @peer type Server <: {type Tie <: Multiple[Client]}
  @peer type Client <: {type Tie <: Single[Server]}

  val enterGroup: Evt[String] on Client = Evt[String]
  val groups: Local[Signal[Map[Remote[Client], String]]] on Server =
    enterGroup.asLocalFromAllSeq.fold(Map.empty[Remote[Client], String]) {_ + _}

  val sendMessage: Evt[Message] on Client = Evt[Message]
  val receivedMessage: Event[Message] per Client on Server = (receiver: Remote[Client]) =>
    sendMessage.asLocalFromAllSeq collect {
      case (sender, message) if sender != receiver && groups()(sender) == groups()(receiver) =>
        message
    }

  def main(): Unit on Client = {
    receivedMessage.asLocal observe println

    def changeGroup(): Unit = {
      println("Enter group to join:")
      enterGroup fire readLine()
    }

    def readNewUsername(): String = {
      println("Enter your username")
      readLine()
    }

    var username = readNewUsername()
    changeGroup()
    println("Enter 'changeGroup', 'changeUsername' or a message")
    while (multitier.running) {
      readLine() match {
        case "changeGroup" => changeGroup()
        case "changeUsername" => username = readNewUsername()
        case input => sendMessage fire Message(input, username, Calendar.getInstance.getTimeInMillis)
      }
    }
  }
}


object Server extends App {
  multitier start new Instance[GroupChat.Server](
    listen[GroupChat.Client] {
      TCP(43053)
    })
}

object Client extends App {
  multitier start new Instance[GroupChat.Client](
    connect[GroupChat.Server] {
      TCP("localhost", 43053)
    })
}