# firewall for the ec2 instance: http open to everyone, ssh limited by ssh_cidr
resource "aws_security_group" "app" {
  name = "proofbase-app"
  description = "proofbase application instance"
  vpc_id = data.aws_vpc.default.id

  ingress {
    description = "HTTP"
    from_port = 80
    to_port = 80
    protocol = "tcp"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ingress {
    description = "SSH"
    from_port = 22
    to_port = 22
    protocol = "tcp"
    cidr_blocks = [var.ssh_cidr]
  }

  egress {
    from_port = 0
    to_port = 0
    protocol = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }
}

# firewall for the db: postgres reachable only from the app instance, nothing else
resource "aws_security_group" "db" {
  name = "proofbase-db"
  description = "Postgres, reachable only from the app instance"
  vpc_id = data.aws_vpc.default.id

  ingress {
    description = "Postgres from app"
    from_port = 5432
    to_port = 5432
    protocol = "tcp"
    security_groups = [aws_security_group.app.id]
  }
}
